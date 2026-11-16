// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;

use super::*;

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
        let owner = tcx
            .hir_crate_items(())
            .owners()
            .map(|owner| owner.def_id.to_def_id())
            .find(|owner| {
                tcx.opt_item_name(*owner)
                    .is_some_and(|name| name.as_str() == "Target")
            })
            .expect("actual native Target declaration");
        let checked = check(tcx, owner);
        let mut result = checked.observation();
        if matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
            result["headers"] =
                super::super::declaration_headers::check(tcx, owner.expect_local()).observation();
        }
        let wrong = tcx
            .hir_crate_items(())
            .owners()
            .map(|owner| owner.def_id.to_def_id())
            .find(|owner| {
                tcx.opt_item_name(*owner)
                    .is_some_and(|name| name.as_str() == "Other")
            })
            .expect("actual other native owner");
        result["wrong_owner_accepted"] = json!(checked.for_owner(tcx, wrong).is_some());
        let owned = checked.owned_for(tcx, owner);
        assert_eq!(owned.as_ref(), checked.for_owner(tcx, owner));
        if let Some(owned) = owned {
            assert_eq!(owned.owner(), key(tcx, owner));
            assert_eq!(
                owned.parameters().len(),
                result["parameters"].as_array().unwrap().len()
            );
            assert_eq!(
                owned.clauses().len(),
                result["clauses"].as_array().unwrap().len()
            );
            if let Some(nominal) = owned.nominal() {
                assert_eq!(
                    format!("{:?}", nominal.mode()),
                    result["nominal"]["mode"].as_str().unwrap()
                );
                assert_eq!(
                    nominal.known_sized(),
                    result["nominal"]["known_sized"].as_bool().unwrap()
                );
                assert_eq!(
                    nominal.external_body(),
                    result["nominal"]["external_body"].as_bool().unwrap()
                );
                assert_eq!(
                    nominal.ext_equal_declared(),
                    result["nominal"]["ext_equal_declared"].as_bool().unwrap()
                );
                assert_eq!(nominal.recursion().len(), owned.parameters().len());
            }
        }
        self.result = Some(result);
        Compilation::Stop
    }
}

#[test]
fn native_nominal_mode_keeps_the_first_declared_mode() {
    for (attributes, expected) in [
        ("", "Exec"),
        ("#[verus::internal(spec)]", "Spec"),
        ("#[verus::internal(proof)]", "Proof"),
        ("#[verus::internal(spec)] #[verus::internal(exec)]", "Spec"),
        ("#[verus::internal(exec)] #[verus::internal(spec)]", "Exec"),
    ] {
        let result = native(&format!(
            "#[verus::internal(verus_macro)] {attributes} pub struct Target;"
        ));
        assert_eq!(result["state"], "CheckedNativeGenericPolicy");
        assert_eq!(result["nominal"]["mode"], expected);
    }
}

/// The markers deliberately exercise native syntax/predicates only. They do
/// not stand in for authenticated proc-macro output or grant import authority.
fn native(source: &str) -> Value {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-policy-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let path = directory.0.join("policy.rs");
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
    let arguments = vec![
        "native-policy-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_policy_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ];
    let mut capture = Capture::default();
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut capture))
        .expect("the ordinary native Rust fixture must compile");
    let result = capture
        .result
        .expect("the genuine native analysis callback ran");
    assert_eq!(result["wrong_owner_accepted"], false);
    if result["state"] != "Unknown" {
        assert_eq!(result["import_authorized"], false);
    }
    result
}

#[test]
fn uninterpreted_policy_requires_the_complete_spec_declaration() {
    let marker = "#[verus::internal(verus_macro)]";
    for (directives, accepted) in [
        ("#[verus::internal(spec)] #[verus::internal(uninterp)] #[verus::internal(external_body)]", true),
        ("#[verus::internal(exec)] #[verus::internal(uninterp)] #[verus::internal(external_body)]", false),
        ("#[verus::internal(proof)] #[verus::internal(uninterp)] #[verus::internal(external_body)]", false),
        ("#[verus::internal(spec)] #[verus::internal(uninterp)]", false),
        ("#[verus::internal(spec)] #[verus::internal(external_body)]", false),
        ("#[verus::internal(spec)] #[verus::internal(uninterp)] #[verus::internal(external_body)] #[verus::internal(open)]", false),
        ("#[verus::internal(spec)] #[verus::internal(uninterp(argument))] #[verus::internal(external_body)]", false),
    ] {
        let result = native(&format!(
            "{marker} {directives} pub fn Target<A>(value: A) -> u64 {{ unimplemented!() }}"
        ));
        assert_eq!(result["state"] == "CheckedNativeGenericPolicy", accepted, "{result}");
        if accepted {
            assert_eq!(result["parameters"][0]["native_index"], 0);
            assert_eq!(result["headers"]["state"], "ObservedNoHeaderReference");
            assert_eq!(result["headers"]["bodies_visited"], 1);
        }
    }
}

#[test]
fn an_uninterpreted_signature_does_not_hide_original_header_calls() {
    let result = native(
        r#"
#[rustc_diagnostic_item = "verus::verus_builtin::requires"]
fn Header<T>(value: T) {}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
#[verus::internal(uninterp)] #[verus::internal(external_body)]
pub fn Target<A>(value: A) -> u64 { Header((true,)); unimplemented!() }
"#,
    );
    assert_eq!(result["state"], "CheckedNativeGenericPolicy");
    assert_eq!(result["headers"]["state"], "ObservedHeaderReferences");
    assert_eq!(result["headers"]["references"][0]["kind"], "Requires");
}

#[test]
fn native_sizedness_and_named_recursion_are_scoped_to_the_real_owner() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#,
    );
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    assert_eq!(result["nominal"]["known_sized"], true);
    assert_eq!(result["nominal"]["ext_equal_declared"], true);
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["policy"],
        "Reject"
    );
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["origin"],
        "ItemAttribute"
    );
    assert!(result["clauses"]
        .as_array()
        .unwrap()
        .iter()
        .any(|clause| clause["kind"] == "Sized" && clause["native_parameter_index"] == 0));
}

#[test]
fn native_parent_and_function_binders_keep_their_complete_indices() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
struct Carrier<A> { marker: std::marker::PhantomData<A> }
impl<A> Carrier<A> {
    #[verus::internal(verus_macro)]
    pub fn Target<B>(self, _value: B) {}
}
"#,
    );
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    let parameters = result["parameters"].as_array().unwrap();
    assert_eq!(parameters.len(), 2);
    assert_eq!(parameters[0]["native_index"], 0);
    assert_eq!(parameters[1]["native_index"], 1);
    assert_ne!(parameters[0]["scope"], parameters[1]["scope"]);
    for index in [0, 1] {
        assert!(result["clauses"]
            .as_array()
            .unwrap()
            .iter()
            .any(|clause| clause["kind"] == "Sized" && clause["native_parameter_index"] == index));
    }
}

#[test]
fn a_user_trait_named_sized_does_not_supply_the_native_lang_item() {
    let result = native(
        r#"
trait Sized {}
#[verus::internal(verus_macro)]
pub fn Target<T: Sized>(_value: T) {}
"#,
    );
    assert_eq!(result["state"], "Unknown");
    assert!(result["reason"]
        .as_str()
        .unwrap()
        .contains("recognized native sizedness lang item"));
}

#[test]
fn lifetime_const_and_projection_require_distinct_policy_producers() {
    for source in [
        "#[verus::internal(verus_macro)] pub fn Target<'a>(_value: &'a bool) {}",
        "#[verus::internal(verus_macro)] pub fn Target<'unused>() {}",
        "#[verus::internal(verus_macro)] pub fn Target(_value: &bool) {}",
        "#[verus::internal(verus_macro)] pub fn Target<const N: usize>() {}",
        "#[verus::internal(verus_macro)] pub fn Target<T: 'static>() {}",
        "#[verus::internal(verus_macro)] pub const fn Target() {}",
        "trait Assoc { type Value; } #[verus::internal(verus_macro)] pub fn Target<T: Assoc>() where T::Value: Copy {}",
    ] {
        let result = native(source);
        assert_eq!(result["state"], "Unknown", "{source}: {result}");
    }
}

#[test]
fn native_dst_and_meta_sized_do_not_turn_into_known_sized() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
pub struct Target<A: ?Sized> { tail: A }
"#,
    );
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    assert_eq!(result["nominal"]["known_sized"], false);
    assert!(!result["clauses"]
        .as_array()
        .unwrap()
        .iter()
        .any(|clause| clause["kind"] == "Sized" && clause["native_parameter_index"] == 0));
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["policy"],
        "RejectInGround"
    );
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["origin"],
        "VerusDefault"
    );
}

#[test]
fn an_external_body_needs_each_explicit_parameter_policy() {
    let template = r#"
#[verus::internal(verus_macro)]
#[verifier::external_body]
POLICY
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#;
    assert_eq!(native(&template.replace("POLICY", ""))["state"], "Unknown");
    let result = native(&template.replace("POLICY", "#[verifier::reject_recursive_types(A)]"));
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    assert_eq!(result["nominal"]["external_body"], true);
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["policy"],
        "Reject"
    );
}

#[test]
fn duplicates_unknown_names_and_unclassified_directives_stay_unknown() {
    for directives in [
        "#[verifier::reject_recursive_types(A)] #[verifier::accept_recursive_types(A)]",
        "#[verifier::reject_recursive_types(B)]",
        "#[verifier::reject_recursive_types(A, B)]",
        "#[verifier::type_invariant]",
    ] {
        let source = format!("#[verus::internal(verus_macro)] {directives} pub struct Target<A> {{ marker: std::marker::PhantomData<A> }}");
        assert_eq!(native(&source)["state"], "Unknown");
    }
}

#[test]
fn all_three_named_policies_follow_native_indices_instead_of_attribute_order() {
    let result = native(
        r#"
#[verus::internal(verus_macro)]
#[verifier::accept_recursive_types(C)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types_in_ground_variants(B)]
pub struct Target<A, B, C> { marker: std::marker::PhantomData<(A, B, C)> }
"#,
    );
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    for (index, policy) in [(0, "Reject"), (1, "RejectInGround"), (2, "Accept")] {
        let entry = &result["nominal"]["parameter_recursion"][index];
        assert_eq!(entry["native_parameter_index"], index);
        assert_eq!(entry["policy"], policy);
    }
}

#[test]
fn parameter_flags_keep_verus_precedence_and_item_duplicates_are_unknown() {
    let source = r#"
#[verus::internal(verus_macro)]
pub struct Target<#[verifier::accept_recursive_types] #[verifier::reject_recursive_types] A> {
    marker: std::marker::PhantomData<A>
}
"#;
    let result = native(source);
    assert_eq!(result["state"], "CheckedNativeGenericPolicy", "{result}");
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["policy"],
        "Reject"
    );
    assert_eq!(
        result["nominal"]["parameter_recursion"][0]["origin"],
        "ParameterAttribute"
    );
    let source = format!("#[verifier::reject_recursive_types(A)] {source}");
    assert_eq!(native(&source)["state"], "Unknown");
}
