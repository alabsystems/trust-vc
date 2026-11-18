//! Real builtin-derived Clone calls retain ordinary body and mode authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) -> common::Run {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert_clone_body_proved(&result);
    result
}

fn assert_clone_body_proved(result: &common::Run) {
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| {
                f["kind"] == "AssocFn"
                    && f["def_path"]
                        .as_str()
                        .is_some_and(|p| p.ends_with("::clone"))
                    && f["verdict"] == "verified"
                    && f["sites_proved"].as_u64().unwrap_or(0) > 0
            }),
        "the actual local Clone body obligation must be proved: {result:?}"
    );
}

fn no_verification(result: &common::Run) {
    assert_eq!(result.exit, 1, "{result:?}");
    assert_ne!(result.outcome(), "checked", "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .is_none_or(|fns| { fns.iter().all(|f| f["verdict"] != "verified") }),
        "{result:?}"
    );
}

fn refused(result: &common::Run) {
    no_verification(result);
    assert_eq!(
        result.outcome(),
        "refused",
        "the valid native input must reach a reader refusal: {result:?}"
    );
}

#[test]
fn exact_retained_clone_match_cast_composite_and_false_twin() {
    // This is byte-exactly the original failed composite, including its
    // prelude; changing it to an enum-value parameter would miss CloneCALL.
    let source = include_str!("fixtures/clone_call_match.rs");
    let positive = common::run_raw("clone_match_original", source, &[]);
    assert_eq!(positive.exit, 0, "{positive:?}");
    assert_eq!(positive.outcome(), "checked", "{positive:?}");
    assert_clone_body_proved(&positive);
    let false_source = source.replace("assert(b == 9u8)", "assert(b == 3u8)");
    assert_ne!(false_source, source);
    let negative = common::run_raw("clone_match_false", &false_source, &[]);
    assert_eq!(negative.exit, 1, "{negative:?}");
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert!(
        negative.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["sites_failed"].as_u64().unwrap_or(0) > 0),
        "{negative:?}"
    );
}

#[test]
fn shared_receiver_ufcs_and_two_enum_selections() {
    checked(
        "clone_calls_ufcs",
        "verus! {
        #[derive(Copy, Clone)] enum E { A = 3, B = 9 }
        #[derive(Copy, Clone)] enum F { A = 20, B = 24 }
        fn test(e: E, f: F) {
            let a = e.clone();
            let b = E::clone(&e);
            let c = <E as Clone>::clone(&e);
            let d = f.clone();
            assert(a as u8 == e as u8);
            assert(b as u8 == e as u8);
            assert(c as u8 == e as u8);
            assert(d as u8 == f as u8);
        }
    }",
    );
}

#[test]
fn effectful_receiver_is_evaluated_once_and_false_count_fails() {
    let source = "verus! {
        #[derive(Copy, Clone)] enum E { A = 3, B = 9 }
        fn test() {
            let mut count: u8 = 0;
            let copied = ({ count += 1; E::B }).clone();
            assert(count == 1);
            assert(copied as u8 == 9);
        }
    }";
    checked("clone_call_once", source);
    let negative = common::run(
        "clone_call_once_false",
        &source.replace("count == 1", "count == 2"),
        &[],
    );
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert_eq!(negative.exit, 1, "{negative:?}");
}

#[test]
fn unrelated_generic_caller_bounds_are_retained() {
    checked(
        "clone_call_generic_caller",
        "verus! {
        #[derive(Copy, Clone)] enum E { A = 3, B = 9 }
        fn copy<T: Copy>(e: E) -> (r: u8) ensures r == e as u8, {
            let c = e.clone(); c as u8
        }
        fn test() { let n = copy::<bool>(E::B); assert(n == 9); }
    }",
    );
}

#[test]
fn manual_forged_and_same_named_user_derives_gain_no_call_authority() {
    for (name, marker) in [
        ("clone_call_manual", ""),
        ("clone_call_forged", "#[automatically_derived]"),
    ] {
        let source = format!(
            "verus! {{
            #[derive(Copy)] enum E {{ A = 3, B = 9 }}
            {marker} impl Clone for E {{ fn clone(&self) -> Self {{ E::A }} }}
            fn test(e: E) {{ let c = e.clone(); assert(c as u8 == e as u8); }}
        }}"
        );
        refused(&common::run(name, &source, &[]));
    }
    let image =
        std::env::var("TRUST_VC_ENUM_CLONE_SPOOF").expect("genuine same-toolchain derive fixture");
    let operand = format!("enum_clone_spoof={image}");
    refused(&common::run(
        "clone_call_user_derive",
        "
        use enum_clone_spoof::Clone;
        verus! {
            #[derive(Copy, Clone)] enum E { A, B }
            fn test(e: E) { let c = e.clone(); assert(c as u8 == e as u8); }
        }",
        &["--extern", &operand],
    ));
}

#[test]
fn other_clone_shapes_and_methods_remain_closed() {
    for (name, source) in [
        (
            "clone_call_reference",
            "verus! {
            #[derive(Copy, Clone)] enum E { A, B }
            fn test(e: E) { let r = &e; let c = Clone::clone(&r); }
        }",
        ),
        (
            "clone_call_tuple",
            "verus! { fn test(x: (u8, bool)) { let c = x.clone(); } }",
        ),
        (
            "clone_call_foreign",
            "verus! { fn test(x: Option<u8>) { let c = x.clone(); } }",
        ),
        (
            "clone_call_from",
            "verus! {
            #[derive(Copy, Clone)] enum E { A, B }
            fn test(mut e: E) { e.clone_from(&E::B); }
        }",
        ),
        (
            "clone_call_fields",
            "verus! {
            #[derive(Copy, Clone)] enum E { A(u8), B }
            fn test(e: E) { let c = e.clone(); }
        }",
        ),
        (
            "clone_call_generic_enum",
            "verus! {
            #[derive(Copy, Clone)] enum E<T> { A(T), B }
            fn test(e: E<u8>) { let c = e.clone(); }
        }",
        ),
        (
            "clone_call_empty",
            "verus! {
            #[derive(Copy, Clone)] enum E {}
            fn test(e: E) { let c = e.clone(); }
        }",
        ),
        (
            "clone_call_opaque",
            "verus! {
            #[verifier::external_body] #[derive(Copy, Clone)] enum E { A, B }
            fn test(e: E) { let c = e.clone(); }
        }",
        ),
    ] {
        refused(&common::run(name, source, &[]));
    }
}

#[test]
fn a_same_named_inherent_method_keeps_its_own_contract() {
    let result = common::run(
        "clone_call_inherent",
        "verus! {
        #[derive(Copy, Clone)] enum E { A = 3, B = 9 }
        impl E {
            fn clone(&self) -> (r: Self) ensures r as u8 == 3, { E::A }
        }
        fn test() { let e = E::B; let c = e.clone(); assert(c as u8 == 9); }
    }",
        &[],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
}

#[test]
fn exec_calls_still_obey_ghost_and_spec_modes() {
    for (name, function) in [
        (
            "clone_call_in_proof",
            "proof fn test(e: E) { let c = e.clone(); }",
        ),
        (
            "clone_call_in_spec",
            "spec fn test(e: E) -> E { e.clone() }",
        ),
    ] {
        let source = format!("verus! {{ #[derive(Copy, Clone)] enum E {{ A, B }} {function} }}");
        no_verification(&common::run(name, &source, &[]));
    }
}

#[test]
fn ordinary_native_borrow_error_cannot_reach_verification() {
    let result = common::run(
        "clone_call_borrow_error",
        "verus! {
        #[derive(Copy, Clone)] enum E { A = 3, B = 9 }
        fn test() {
            let mut e = E::B;
            let reference = &e;
            e = E::A;
            let c = E::clone(reference);
            assert(c as u8 == 9);
        }
    }",
        &[],
    );
    no_verification(&result);
    assert_eq!(
        result.record["erase_exit"], 1,
        "must reach the real native lifetime check: {result:?}"
    );
}
