//! Native enum cast values and checked built-in Clone bodies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) -> common::Run {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["verdict"] == "verified"),
        "{result:?}"
    );
    result
}

#[test]
fn actual_discriminants_keep_explicit_gaps_and_destination_types() {
    checked(
        "enum_discriminants",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 255, C }
        proof fn literals() {
            assert(E::A as int == 0);
            assert(E::B as int == 255);
            assert(E::C as int == 256);
        }
        fn symbolic(e: E) -> (r: u16)
            ensures r == e as int, r == 0 || r == 255 || r == 256
        { e as u16 }
    }",
    );
}

#[test]
fn genuine_builtin_copy_clone_is_an_ordinary_verified_body() {
    let result = checked(
        "enum_builtin_clone",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 255, C }
        fn cast(e: E) -> (r: usize)
            ensures r == e as int, r == 0 || r == 255 || r == 256
        { e as usize }
    }",
    );
    let functions = result.record["functions"].as_array().unwrap();
    let clone = functions
        .iter()
        .find(|f| {
            f["def_path"]
                .as_str()
                .is_some_and(|s| s.ends_with("::clone"))
        })
        .expect("actual derived Clone record");
    assert_eq!(clone["verdict"], "verified", "{result:?}");
    assert!(
        clone["sites_proved"].as_u64().unwrap_or(0) > 0,
        "{result:?}"
    );
}

#[test]
fn false_discriminants_and_false_cast_results_fail() {
    for (name, source) in [
        (
            "enum_false_gap",
            "verus! {
            #[derive(Copy, Clone)] enum E { A, B = 255, C }
            proof fn test() { assert(E::C as int == 2); }
        }",
        ),
        (
            "enum_false_result",
            "verus! {
            #[derive(Copy, Clone)] enum E { A, B = 255, C }
            fn test(e: E) -> (r: u16) ensures r == 2 { e as u16 }
        }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
    }
}

#[test]
fn source_effects_are_evaluated_once() {
    checked(
        "enum_once",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 255 }
        fn test() {
            let mut count: u8 = 0;
            let value = ({ count += 1; E::B }) as u16;
            assert(count == 1);
            assert(value == 255);
        }
    }",
    );
    let result = common::run(
        "enum_once_false",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 255 }
        fn test() {
            let mut count: u8 = 0;
            let value = ({ count += 1; E::B }) as u16;
            assert(count == 2);
        }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
}

#[test]
fn empty_and_payload_enums_are_not_castable() {
    for (name, source, message) in [
        (
            "enum_empty",
            "verus! { #[derive(Copy, Clone)] enum E {} proof fn test(e: E) { let i = e as int; } }",
            "Zero-sized empty Enum expr",
        ),
        (
            "enum_payload",
            "verus! { #[derive(Copy, Clone)] enum E { A(bool), B } proof fn test(e: E) { let i = e as int; } }",
            "Enum variant should not contain any fields.",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(
            result
                .errors()
                .iter()
                .any(|error| error.message.contains(message)),
            "{result:?}"
        );
        assert!(result.record["functions"].as_array().unwrap().iter()
            .all(|f| f["verdict"] != "verified"), "{result:?}");
    }
}

#[test]
fn user_derived_marker_and_poisoned_manual_clone_gain_no_eligibility() {
    for (name, body) in [
        ("enum_forged_clone", "*self"),
        ("enum_poisoned_clone", "E::A"),
    ] {
        let source = format!(
            "verus! {{
            #[derive(Copy)] enum E {{ A, B }}
            #[automatically_derived]
            impl Clone for E {{ fn clone(&self) -> Self {{ {body} }} }}
            proof fn test() {{ assert(E::B as int == 1); }}
        }}"
        );
        let result = common::run(name, &source, &[]);
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|f| f["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn a_same_named_user_derive_is_not_the_compiler_builtin() {
    // Build tests/fixtures/enum_clone_spoof with this same genuine native
    // toolchain, then supply its actual proc-macro image, like the builtins.
    let image = std::env::var("TRUST_VC_ENUM_CLONE_SPOOF")
        .expect("set TRUST_VC_ENUM_CLONE_SPOOF to the same-toolchain fixture proc macro");
    let operand = format!("enum_clone_spoof={image}");
    let result = common::run(
        "enum_user_derive",
        "
        use enum_clone_spoof::Clone;
        verus! {
            #[derive(Copy, Clone)] enum E { A, B }
            proof fn test() { assert(E::B as int == 1); }
        }
    ",
        &["--extern", &operand],
    );
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|f| f["verdict"] != "verified"),
        "{result:?}"
    );
}

#[test]
fn casts_preserve_modes_and_ordinary_narrowing_abstraction() {
    let mode = common::run(
        "enum_bad_mode",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B }
        spec fn hidden() -> E { E::B }
        fn test() -> u8 { hidden() as u8 }
    }",
        &[],
    );
    assert_eq!(mode.outcome(), "verus-rejected", "{mode:?}");
    checked(
        "enum_in_range",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 255 }
        proof fn test() { assert(E::B as u8 == 255); }
    }",
    );
    let narrowing = common::run(
        "enum_out_of_range",
        "verus! {
        #[derive(Copy, Clone)] enum E { A, B = 256 }
        proof fn test() { assert(E::B as u8 == 0); }
    }",
        &[],
    );
    assert_eq!(narrowing.outcome(), "verification-failed", "{narrowing:?}");
}
