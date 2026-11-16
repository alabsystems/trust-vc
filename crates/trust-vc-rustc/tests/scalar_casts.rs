//! Native Boolean casts retain their scalar semantics, effects and mode checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|function| { function["verdict"] == "verified" }),
        "{result:?}"
    );
}

#[test]
fn original_boolean_to_integer_assertions() {
    // The unchanged body of A40 integers::test_bool_to_int.
    checked(
        "original_bool_to_int",
        "verus! {
        fn test1() {
            assert(true as usize == 1);
            assert(false as usize == 0);
            assert(false as int == 0);
        }
    }",
    );
}

#[test]
fn symbolic_casts_keep_both_boolean_values_and_destination_types() {
    checked(
        "symbolic_bool_casts",
        "verus! {
        proof fn symbolic(b: bool) {
            assert((b as int == 1) == b);
            assert((b as nat == 0) == !b);
            assert((b as u8 == 1) == b);
            assert((b as i8 == 0) == !b);
            assert(b as usize <= 1);
        }
        fn executable(b: bool) -> (r: u8) ensures (r == 1) == b { b as u8 }
    }",
    );
}

#[test]
fn false_integer_values_are_actual_proof_failures() {
    for (name, source) in [
        (
            "false_bool_literal",
            "verus! { proof fn test() { assert(false as int == 1); } }",
        ),
        (
            "false_bool_variable",
            "verus! { proof fn test(b: bool) { assert(b as u8 == 2); } }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(result.errors().len(), 1, "{result:?}");
        assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
    }
}

#[test]
fn cast_operand_effects_run_once() {
    checked(
        "bool_cast_effect_once",
        "verus! {
        fn test() {
            let mut x: u8 = 0;
            let result = ({ x += 1; x == 1 }) as u8;
            assert(x == 1);
            assert(result == 1);
        }
    }",
    );
    let result = common::run(
        "bool_cast_effect_false",
        "verus! {
        fn test() {
            let mut x: u8 = 0;
            let result = ({ x += 1; x == 1 }) as u8;
            assert(x == 2);
        }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
}

#[test]
fn boolean_cast_does_not_launder_spec_values_into_exec() {
    let result = common::run(
        "bool_cast_spec_in_exec",
        "verus! {
        spec fn hidden() -> bool { true }
        fn bad() -> u8 { hidden() as u8 }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    assert!(!result.errors().is_empty(), "{result:?}");
}

#[test]
fn unsupported_cast_sources_and_destinations_stay_rejected() {
    for (name, source) in [
        (
            "float_source",
            "verus! { fn test(x: f64) -> u8 { x as u8 } }",
        ),
        ("char_source", "verus! { fn test() -> u32 { 'a' as u32 } }"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
    for (name, source) in [
        (
            "bool_to_float",
            "verus! { fn test(x: bool) -> f64 { x as f64 } }",
        ),
        (
            "bool_to_char",
            "verus! { fn test(x: bool) -> char { x as char } }",
        ),
        (
            "int_to_bool",
            "verus! { fn test(x: u8) -> bool { x as bool } }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "front-end-rejected", "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
    checked(
        "integer_cast_regression",
        "verus! {
        proof fn test() { assert(1u16 as u8 == 1); assert(255u8 as u16 == 255); }
    }",
    );
    // Ordinary Verus scalar casts choose an in-range value outside the range;
    // Boolean support must not turn that existing choice into Rust wrapping.
    let result = common::run(
        "integer_cast_out_of_range",
        "verus! { proof fn test() { assert(256u16 as u8 == 0); } }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
}
