//! Known declaration errors close only their actual invalid source owner.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

const MUTABLE: &str = "when_used_as_spec not supported for function with &mut param";
const MISSING: &str = "cannot find function referred to in when_used_as_spec";

fn no_verified_or_proved(result: &common::Run) {
    assert!(result.record["functions"].as_array().unwrap().iter().all(|function| {
        function["verdict"] != "verified"
            && function["sites_proved"].as_u64().unwrap_or(0) == 0
            && function["sites_failed"].as_u64().unwrap_or(0) == 0
    }), "{result:?}");
}

fn rejected_once(name: &str, source: &str, args: &[&str], message: &str) {
    let result = common::run(name, source, args);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].code, None, "{result:?}");
    assert!(errors[0].message.contains(message), "{result:?}");
    no_verified_or_proved(&result);
}

fn refused_without(name: &str, source: &str, args: &[&str], message: &str) {
    let result = common::run(name, source, args);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(!result.errors().iter().any(|error| error.message.contains(message)), "{result:?}");
    no_verified_or_proved(&result);
}

#[test]
fn a_missing_trait_sibling_does_not_resolve_to_a_free_or_other_trait_function() {
    for (name, source) in [
        ("original", "verus! {
            spec fn f() -> bool { true }
            trait T { #[verifier::when_used_as_spec(f)] fn g() -> bool { false } }
        }"),
        ("absent", "verus! {
            trait T { #[verifier::when_used_as_spec(absent)] fn g() -> bool { false } }
        }"),
        ("other_trait", "verus! {
            trait U { fn f() -> bool { true } }
            trait T { #[verifier::when_used_as_spec(f)] fn g() -> bool { false } }
        }"),
    ] {
        rejected_once(&format!("autospec_trait_missing_{name}"), source, &[], MISSING);
    }
}

#[test]
fn any_same_trait_member_and_trait_impl_source_keep_their_mapping_refusal() {
    for (name, source) in [
        ("spec_fn", "verus! { trait T {
            spec fn f() -> bool { true }
            #[verifier::when_used_as_spec(f)] fn g() -> bool { false }
        } }"),
        ("exec_fn", "verus! { trait T {
            fn f() -> bool { true }
            #[verifier::when_used_as_spec(f)] fn g() -> bool { false }
        } }"),
        ("constant", "verus! { trait T {
            const f: bool = true;
            #[verifier::when_used_as_spec(f)] fn g() -> bool { false }
        } }"),
        ("trait_impl", "verus! {
            spec fn f() -> bool { true }
            trait T { fn g() -> bool; }
            impl T for bool { #[verifier::when_used_as_spec(f)] fn g() -> bool { false } }
        }"),
    ] {
        refused_without(&format!("autospec_trait_present_{name}"), source, &[], MISSING);
    }
}

#[test]
fn top_level_mutable_parameters_are_rejected_once_before_target_or_body_read() {
    for (name, source) in [
        ("original", "verus! {
            pub open spec fn d_spec(a: &mut bool) -> bool { *a }
            #[verifier::when_used_as_spec(d_spec)] pub fn d(a: &mut bool) -> bool { *a }
        }"),
        ("missing_target", "verus! {
            #[verifier::when_used_as_spec(absent)] fn source(a: &mut bool) -> bool { true }
        }"),
        ("generic", "verus! {
            spec fn target<T>(a: &mut T) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source<T>(a: &mut T) -> bool { true }
        }"),
        ("inherent_mut_ref_self", "verus! { struct S {} impl S {
            spec fn target(&mut self) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source(&mut self) -> bool { true }
        } }"),
    ] {
        rejected_once(&format!("autospec_mutable_rejected_{name}"), source, &["-V", "new-mut-ref"], MUTABLE);
    }
}

#[test]
fn nonmatching_roles_options_and_parameter_shapes_do_not_gain_permissions() {
    for (name, source, args) in [
        ("no_attribute", "verus! { fn source(a: &mut bool) -> bool { true } }", &["-V", "new-mut-ref"][..]),
        ("no_macro", "#[verifier::when_used_as_spec(absent)] fn source(a: &mut bool) -> bool { true }", &["--no-external-by-default", "-V", "new-mut-ref"][..]),
        ("nested", "verus! {
            spec fn target(a: &&mut bool) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source(a: &&mut bool) -> bool { true }
        }", &["-V", "new-mut-ref"][..]),
        ("old_mode", "verus! {
            spec fn target(a: &mut bool) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source(a: &mut bool) -> bool { true }
        }", &[][..]),
        ("unknown_pointee", "verus! {
            spec fn target(a: &mut *const bool) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source(a: &mut *const bool) -> bool { true }
        }", &["-V", "new-mut-ref"][..]),
        ("binding_mut_self", "verus! { struct S {} impl S {
            spec fn target(mut self, a: &mut bool) -> bool { true }
            #[verifier::when_used_as_spec(target)] fn source(mut self, a: &mut bool) -> bool { true }
        } }", &["-V", "new-mut-ref"][..]),
    ] {
        refused_without(&format!("autospec_mutable_nonmatch_{name}"), source, args, MUTABLE);
    }
}

#[test]
fn an_external_source_keeps_its_external_role() {
    let result = common::run("autospec_rejection_external_control", "verus! {
        #[verifier::external]
        #[verifier::when_used_as_spec(absent)] fn source(a: &mut bool) -> bool { true }
    }", &["-V", "new-mut-ref"]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(result.record["functions"].as_array().unwrap().iter().all(|function| {
        function["verdict"] == "external"
    }), "{result:?}");
    no_verified_or_proved(&result);

    let called = common::run("autospec_rejection_external_call_control", "verus! {
        spec fn logical() -> bool { true }
        #[verifier::external]
        #[verifier::when_used_as_spec(logical)] fn actual() -> bool { false }
        proof fn test() { assert(actual()); }
    }", &[]);
    assert_eq!(called.exit, 1, "{called:?}");
    assert_eq!(called.outcome(), "verus-rejected", "{called:?}");
    let errors = called.errors();
    assert_eq!(errors.len(), 1, "{called:?}");
    assert_eq!(errors[0].code, None, "{called:?}");
    assert!(errors[0].message.contains("cannot use function"), "{called:?}");
    assert!(errors[0].message.contains("marked as `external`"), "{called:?}");
    no_verified_or_proved(&called);
}

#[test]
fn a_rejected_source_does_not_suppress_another_owners_mutable_refusal() {
    let result = common::run("autospec_mutable_unrelated_refusal", "verus! {
        spec fn target(a: &mut bool) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source(a: &mut bool) -> bool { true }
        fn unrelated(a: &mut bool) -> bool { true }
    }", &["-V", "new-mut-ref"]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert_eq!(result.errors().iter().filter(|error| error.message == MUTABLE).count(), 1, "{result:?}");
    assert!(result.errors().iter().any(|error| error.message.contains("without native availability and resolution")), "{result:?}");
    no_verified_or_proved(&result);
}

#[test]
fn earlier_first_phase_errors_are_not_replaced_or_reordered() {
    let result = common::run("autospec_mutable_earlier_error", "verus! {
        spec fn earlier() -> bool requires true { true }
        spec fn target(a: &mut bool) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source(a: &mut bool) -> bool { true }
    }", &["-V", "new-mut-ref"]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    let errors = result.errors();
    assert_eq!(errors.len(), 2, "{result:?}");
    assert_eq!(errors[0].message, "spec functions cannot have requires/ensures", "{result:?}");
    assert_eq!(errors[1].message, MUTABLE, "{result:?}");
    no_verified_or_proved(&result);
}

#[test]
fn an_ordinary_nonmutable_pair_is_still_checked() {
    let result = common::run("autospec_rejection_nonmutable_control", "verus! {
        pub open spec fn target(a: &bool) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source(a: &bool) -> bool { false }
        proof fn test(a: &bool) { assert(source(a)); }
    }", &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(result.record["functions"].as_array().unwrap().iter().any(|function| {
        function["def_path"] == "test" && function["verdict"] == "verified" && function["sites_proved"] == 1
    }), "{result:?}");
}
