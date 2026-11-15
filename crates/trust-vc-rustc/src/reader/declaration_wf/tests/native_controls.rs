//! Actual native source/query controls; markers are syntax probes, not macro
//! build authentication. Full real-builtin Set staging remains a separate gate.

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use super::super::super::declaration_policy;
use super::super::{check, key};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

#[derive(Default)]
struct Capture {
    result: Option<Value>,
}
impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let find = |name: &str| {
            tcx.hir_crate_items(())
                .owners()
                .map(|owner| owner.def_id.to_def_id())
                .find(|owner| {
                    tcx.opt_item_name(*owner)
                        .is_some_and(|value| value.as_str() == name)
                })
                .unwrap()
        };
        let target = find("Target");
        let other = find("Other");
        let policy = declaration_policy::check(tcx, target);
        let checked = check(tcx, target, &policy);
        let mut result = checked.observation();
        assert!(checked.for_owner(tcx, other).is_none());
        assert_eq!(
            checked.for_owner(tcx, target).cloned(),
            checked.owned_for(tcx, target)
        );
        if let Some(facts) = checked.owned_for(tcx, target) {
            assert_eq!(facts.owner(), key(tcx, target));
            assert_eq!(
                facts.local_declarations().len(),
                result["local_declarations"].as_array().unwrap().len()
            );
            assert_eq!(
                facts.builtin_requirements().len(),
                result["required_builtin_selections"]
                    .as_array()
                    .unwrap()
                    .len()
            );
        }
        let wrong_policy = declaration_policy::check(tcx, other);
        assert!(check(tcx, target, &wrong_policy)
            .for_owner(tcx, target)
            .is_none());
        result["wrong_owner_accepted"] = json!(false);
        self.result = Some(result);
        Compilation::Stop
    }
}

fn native(source: &str) -> Value {
    let dir = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-wf-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&dir.0).unwrap();
    let path = dir.0.join("datatype.rs");
    std::fs::write(
        &path,
        format!(
            r#"#![feature(register_tool, sized_hierarchy, rustc_attrs)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case, internal_features)]
fn Other() {{}}
{source}
"#
        ),
    )
    .unwrap();
    let argv = vec![
        "native-wf-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_wf_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        dir.0.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ];
    let mut capture = Capture::default();
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut capture))
        .expect("the ordinary native source fixture must compile");
    let result = capture.result.expect("native analysis callback ran");
    assert_eq!(result["wrong_owner_accepted"], false);
    assert_eq!(result["import_authorized"], false);
    result
}

fn accepted(result: &Value) -> bool {
    result["state"] == "CheckedConditionalNativeNominalWf"
}

#[test]
fn private_local_fields_are_validated_without_exporting_a_representation() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
struct Child { private_value: bool }
#[verus::internal(verus_macro)]
pub struct Target { private_child: Child }
"#,
    );
    assert!(accepted(&result), "{result}");
    assert_eq!(result["local_declarations"].as_array().unwrap().len(), 2);
    assert_eq!(result["private_representation_exported"], false);
    assert!(!result.to_string().contains("private_child"));
}

#[test]
fn empty_enums_and_base_free_box_cycles_refuse() {
    for source in [
        r#"#[verus::internal(verus_macro)] enum Target {}"#,
        r#"#[verus::internal(verus_macro)] enum Target { Next(Box<Target>) }"#,
    ] {
        let result = native(source);
        assert!(!accepted(&result), "{result}");
    }
}

#[test]
fn recursive_box_datatype_requires_and_records_the_actual_lang_item() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
enum Target { Stop, Next(Box<Target>) }
"#,
    );
    assert!(accepted(&result), "{result}");
    let selected = result["required_builtin_selections"].as_array().unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0]["role"], "OwnedBox");
}

#[test]
fn unvalidated_foreign_or_local_datatypes_do_not_supply_a_wf_fact() {
    for source in [
        r#"
#[verus::internal(verus_macro)] struct Target { marker: std::marker::PhantomData<bool> }
"#,
        r#"
struct Child { value: bool }
#[verus::internal(verus_macro)] struct Target { child: Child }
"#,
    ] {
        let result = native(source);
        assert!(!accepted(&result), "{result}");
    }
}

#[test]
fn external_body_struct_rule_is_explicit_and_does_not_erase_enum_fields() {
    let value = native(
        r#"
#[verus::internal(verus_macro)] #[verifier::external_body]
struct Target { unsupported: fn(bool) -> bool }
"#,
    );
    assert!(accepted(&value), "{value}");
    for source in [
        r#"
#[verus::internal(verus_macro)] struct Target { unsupported: fn(bool) -> bool }
"#,
        r#"
#[verus::internal(verus_macro)] #[verifier::external_body]
enum Target { Unsupported(fn(bool) -> bool) }
"#,
    ] {
        let value = native(source);
        assert!(!accepted(&value), "{value}");
    }
}

#[test]
fn native_parameter_policy_controls_ground_variants() {
    let value = native(r#"#[verus::internal(verus_macro)] struct Target<A>(A);"#);
    assert!(accepted(&value), "{value}");
    let value = native(
        r#"
#[verus::internal(verus_macro)] #[verifier::accept_recursive_types(A)] struct Target<A>(A);
"#,
    );
    assert!(!accepted(&value), "{value}");
}

#[test]
fn a_local_diagnostic_item_cannot_supply_the_foreign_builtin_license() {
    let value = native(
        r#"
#[rustc_diagnostic_item = "verus::verus_builtin::FnSpec"]
struct Impostor<Args, Output>(std::marker::PhantomData<(Args, Output)>);
#[verus::internal(verus_macro)] struct Target { function: Impostor<(bool,), bool> }
"#,
    );
    assert!(!accepted(&value), "{value}");
}
