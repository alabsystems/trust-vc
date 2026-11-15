//! Actual native source controls for the bounded field-language producer.
//! Source markers exercise syntax; selected macro/build authentication remains
//! a separate genuine producer obligation.

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use super::super::{declaration_policy, declaration_wf};
use super::{attributes, check, key};

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
        let wf = declaration_wf::check(tcx, target, &policy);
        let checked = check(tcx, target, &policy, &wf);
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
                facts.external_mappings().len(),
                result["required_external_mappings"]
                    .as_array()
                    .unwrap()
                    .len()
            );
        }
        let other_policy = declaration_policy::check(tcx, other);
        let other_wf = declaration_wf::check(tcx, other, &other_policy);
        assert!(check(tcx, target, &other_policy, &wf)
            .for_owner(tcx, target)
            .is_none());
        assert!(check(tcx, target, &policy, &other_wf)
            .for_owner(tcx, target)
            .is_none());
        result["wf_state"] = wf.observation()["state"].clone();
        // Test-only parser observations. The owned product handoff deliberately
        // contains no field modes, names or field types.
        result["test_only_field_modes"] = json!(tcx
            .adt_def(target)
            .all_fields()
            .map(|field| attributes::mode(
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(field.did.expect_local()))
            )
            .map(|mode| format!("{mode:?}"))
            .unwrap_or_else(|_| "Unknown".into()))
            .collect::<Vec<_>>());
        self.result = Some(result);
        Compilation::Stop
    }
}

fn native(source: &str) -> Value {
    let dir = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-fields-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&dir.0).unwrap();
    let path = dir.0.join("datatype.rs");
    std::fs::write(
        &path,
        format!(
            r#"#![feature(register_tool, sized_hierarchy, rustc_attrs, allocator_api)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case, internal_features)]
#[verus::internal(verus_macro)] struct Other(bool);
{source}
"#
        ),
    )
    .unwrap();
    let argv = vec![
        "native-fields-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_fields_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        dir.0.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ];
    let mut capture = Capture::default();
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut capture))
        .expect("ordinary Rust field fixture must compile");
    let result = capture.result.expect("native analysis callback ran");
    assert_eq!(result["import_authorized"], false);
    result
}

fn accepted(result: &Value) -> bool {
    result["state"] == "CheckedConditionalNativeFieldLanguage"
}

#[test]
fn original_private_local_fields_are_checked_without_representation_export() {
    let result = native(
        r#"
#[verus::internal(verus_macro)] struct Child { private: bool }
#[verus::internal(verus_macro)] pub struct Target<A>(Child, (A, u8, f32, char), &'static bool);
"#,
    );
    assert!(accepted(&result), "{result}");
    assert_eq!(result["local_declarations"].as_array().unwrap().len(), 2);
    assert_eq!(result["required_external_mappings"], json!([]));
    assert_eq!(result["private_representation_exported"], false);
    assert_eq!(result["field_access_or_constructor_authority"], false);
    assert!(!result.to_string().contains("private_child"));
}

#[test]
fn field_mode_uses_first_mode_and_default_without_invented_mode_ordering() {
    let result = native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)]
struct Target {
    default_exec: bool,
    #[verifier::spec] #[verifier::proof] first_spec: bool,
    #[verifier::proof] #[verifier::spec] first_proof: bool,
    #[verus::internal(exec)] explicit_exec: bool,
    #[verifier::spec(checked,)] checked_spec: bool,
    #[verus::internal(spec[checked],)] internal_checked_spec: bool,
}
"#,
    );
    assert!(accepted(&result), "{result}");
    assert_eq!(
        result["test_only_field_modes"],
        json!(["Exec", "Spec", "Proof", "Exec", "Spec", "Spec"])
    );
}

#[test]
fn ordinary_field_parse_error_defaults_the_complete_mode_list_to_exec() {
    let result = native(
        r#"
#[verus::internal(verus_macro)] struct Target {
    #[verifier::spec] #[verifier::not_a_keyword] bad: bool,
}
"#,
    );
    assert!(accepted(&result), "{result}");
    assert_eq!(result["test_only_field_modes"], json!(["Exec"]));
}

#[test]
fn unmodelled_field_attribute_is_unknown_after_successful_native_wf() {
    let result = native(
        r#"
#[verus::internal(verus_macro)] struct Target {
    #[verifier::trigger = "unmodelled"] value: bool,
}
"#,
    );
    assert_eq!(result["wf_state"], "CheckedConditionalNativeNominalWf");
    assert!(!accepted(&result), "{result}");
    assert_eq!(result["test_only_field_modes"], json!(["Unknown"]));
}

const BOX: &str = r#"
#[verus::internal(verus_macro)] enum Target { Base, Next(Box<Target>) }
"#;
const GLOBAL: &str = r#"
#[verus::internal(verus_macro)] #[verifier::external_type_specification]
#[verifier::external_body] pub struct AllocatorProxy(std::alloc::Global);
"#;

#[test]
fn box_allocator_needs_an_original_exact_external_mapping_even_when_wf_passes() {
    let missing = native(BOX);
    assert_eq!(missing["wf_state"], "CheckedConditionalNativeNominalWf");
    assert!(!accepted(&missing), "{missing}");
    let result = native(&format!("{GLOBAL}\n{BOX}"));
    assert!(accepted(&result), "{result}");
    let mappings = result["required_external_mappings"].as_array().unwrap();
    assert_eq!(mappings.len(), 1);
    assert_ne!(
        mappings[0]["proxy"]["stable_crate_id"],
        mappings[0]["target"]["stable_crate_id"]
    );
    assert!(!mappings[0]["target_svh"].as_str().unwrap().is_empty());
}

#[test]
fn allocator_mapping_is_identity_based_and_allows_a_named_single_field() {
    let wrong = native(&format!(
        r#"
#[verus::internal(verus_macro)] #[verifier::external_type_specification]
#[verifier::external_body] pub struct AllocatorProxy(std::time::Duration);
{BOX}
"#
    ));
    assert!(!accepted(&wrong), "{wrong}");
    let named = GLOBAL.replace(
        "AllocatorProxy(std::alloc::Global);",
        "Renamed { value: std::alloc::Global }",
    );
    let result = native(&format!("{named}\n{BOX}"));
    assert!(accepted(&result), "{result}");
}

#[test]
fn invalid_or_ambiguous_mappings_cannot_be_hidden_by_a_valid_mapping() {
    for changed in [
        GLOBAL.replace("pub struct", "struct"),
        GLOBAL.replace("pub struct", "#[verus::internal(proof)] pub struct"),
        GLOBAL.replace("#[verifier::external_body]", ""),
        GLOBAL.replace(
            "external_type_specification]",
            "external_type_specification()]",
        ),
        GLOBAL.replace(
            "AllocatorProxy(std::alloc::Global)",
            "AllocatorProxy(std::alloc::Global, bool)",
        ),
        GLOBAL.replace(
            "AllocatorProxy(std::alloc::Global)",
            "AllocatorProxy<A>(std::alloc::Global, std::marker::PhantomData<A>)",
        ),
    ] {
        let result = native(&format!("{changed}\n{BOX}"));
        assert_eq!(result["wf_state"], "CheckedConditionalNativeNominalWf");
        assert!(!accepted(&result), "{changed}\n{result}");
    }
    let second = GLOBAL.replace("AllocatorProxy", "AnotherProxy");
    let result = native(&format!("{GLOBAL}\n{second}\n{BOX}"));
    assert!(!accepted(&result), "{result}");
    let bad = second.replace("pub struct", "#[verifier::proof] pub struct");
    let result = native(&format!("{GLOBAL}\n{bad}\n{BOX}"));
    assert!(!accepted(&result), "{result}");
    // These twins discriminate rejecting the malformed second mapping from
    // merely failing to find any usable mapping in the crate.
    for bad in [
        second.replace(
            "external_type_specification]",
            "external_type_specification()]",
        ),
        second.replace(
            "pub struct AnotherProxy(std::alloc::Global);",
            "pub enum AnotherProxy { Value(std::alloc::Global) }",
        ),
    ] {
        let result = native(&format!("{GLOBAL}\n{bad}\n{BOX}"));
        assert_eq!(result["wf_state"], "CheckedConditionalNativeNominalWf");
        assert!(!accepted(&result), "{bad}\n{result}");
    }
}

#[test]
fn external_body_struct_erases_fields_only_under_the_explicit_language_rule() {
    let result = native(
        r#"
#[verus::internal(verus_macro)] #[verifier::external_body]
struct Target { physical: fn(bool) -> bool }
"#,
    );
    assert!(accepted(&result), "{result}");
    let result = native(
        r#"
#[verus::internal(verus_macro)] #[verifier::external_body]
enum Target { Physical(fn(bool) -> bool) }
"#,
    );
    assert!(!accepted(&result), "{result}");
}

#[test]
fn checked_wf_scope_and_unsupported_foreign_fields_remain_required() {
    for source in [
        r#"#[verus::internal(verus_macro)] struct Target(std::marker::PhantomData<bool>);"#,
        r#"struct Child(bool); #[verus::internal(verus_macro)] struct Target(Child);"#,
        r#"#[verus::internal(verus_macro)] enum Target {}"#,
    ] {
        let result = native(source);
        assert!(!accepted(&result), "{source}\n{result}");
    }
}
