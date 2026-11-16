//! Actual native source preprocessing and its explicit disabled mode.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn run(name: &str, source: &str, disabled: bool) -> common::Run {
    let flags = if disabled {
        &["-V", "no-bv-simplify"][..]
    } else {
        &[]
    };
    common::run(name, source, flags)
}

#[test]
fn native_test8_ordinary_query_keeps_false_twin_rejected() {
    for disabled in [false, true] {
        for (name, bound, expected) in [("positive", "0x100", 0), ("false", "0xff", 1)] {
            let source = format!("verus! {{ proof fn test8(b: u32) {{ assert(forall|a: u32, b: u32| #[trigger](a & b) == b & a) by(bit_vector); assert(b & 0xff < 0x100) by(bit_vector); assert(0xff & b < {bound}); }} }}");
            let result = run(&format!("test8_{name}_{disabled}"), &source, disabled);
            assert_eq!(result.exit, expected, "{result:?}");
            if expected == 0 {
                assert_eq!(result.outcome(), "checked", "{result:?}");
                assert!(result.errors().is_empty(), "{result:?}");
            } else {
                assert_eq!(result.outcome(), "verification-failed", "{result:?}");
                assert_eq!(result.errors().len(), 1, "{result:?}");
                assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
            }
        }
    }
}

#[test]
fn original_repeated_division_and_remainder_need_the_actual_preprocessing_mode() {
    let source = "verus! { fn test(x: u32, y: u32) { assert(x % y == x % y) by(bit_vector); assert(x / y == x / y) by(bit_vector); } }";
    let projected = run("bv_reflexive_zero_default", source, false);
    assert_eq!(projected.exit, 0, "{projected:?}");
    assert_eq!(projected.outcome(), "checked", "{projected:?}");
    assert!(projected.errors().is_empty(), "{projected:?}");
    let original = run("bv_reflexive_zero_disabled", source, true);
    assert_eq!(original.outcome(), "verification-failed", "{original:?}");
    assert_eq!(original.errors().len(), 2, "{original:?}");
    assert!(
        original
            .errors()
            .iter()
            .all(|error| error.message == "bitvector assertion not satisfied"),
        "{original:?}"
    );
}

#[test]
fn preconversion_identities_keep_distinct_native_inputs_rejected() {
    for (name, declaration, ty, message) in [
        ("integer", "", "int", "expected finite-width integer"),
        (
            "product",
            "struct X { field: u32 }",
            "X",
            "bit_vector prover cannot handle type `test_crate::X`",
        ),
    ] {
        let same = format!("verus! {{ {declaration} proof fn test(x: {ty}) {{ assert(x == x) by(bit_vector); }} }}");
        let projected = run(&format!("bv_same_{name}"), &same, false);
        assert_eq!(projected.outcome(), "checked", "{projected:?}");
        assert_eq!(projected.exit, 0, "{projected:?}");
        let disabled = run(&format!("bv_same_{name}_disabled"), &same, true);
        assert_eq!(disabled.outcome(), "refused", "{disabled:?}");
        assert!(
            disabled
                .errors()
                .iter()
                .any(|error| error.message.contains(message)),
            "{disabled:?}"
        );

        let distinct = format!("verus! {{ {declaration} proof fn test(x: {ty}, y: {ty}) {{ assert(x == y) by(bit_vector); }} }}");
        for disabled in [false, true] {
            let rejected = run(
                &format!("bv_distinct_{name}_{disabled}"),
                &distinct,
                disabled,
            );
            assert_eq!(rejected.outcome(), "refused", "{rejected:?}");
            assert!(
                rejected
                    .errors()
                    .iter()
                    .any(|error| error.message.contains(message)),
                "{rejected:?}"
            );
        }
    }
}

#[test]
fn preprocessing_keeps_false_relations_failed_and_declared_arbitrary_values_available() {
    let false_relation =
        "verus! { proof fn test(x: u32, y: u32) { assert(x / y != x / y) by(bit_vector); } }";
    for disabled in [false, true] {
        let result = run(
            &format!("bv_false_identity_{disabled}"),
            false_relation,
            disabled,
        );
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(result.errors().len(), 1, "{result:?}");
    }

    // A declared local has an arbitrary represented value before assignment.
    // The VcIR unit control separately checks a genuinely absent Reads entry.
    let arbitrary = "verus! { proof fn test() { let x: u32; assert(x == x) by(bit_vector); } }";
    for disabled in [false, true] {
        let accepted = run(
            &format!("bv_arbitrary_identity_{disabled}"),
            arbitrary,
            disabled,
        );
        assert_eq!(accepted.outcome(), "checked", "{accepted:?}");
        assert_eq!(accepted.exit, 0, "{accepted:?}");
    }
}

#[test]
fn dead_or_pruned_source_keeps_the_isolated_prover_and_preconversion_policy() {
    for (name, source) in [
        (
            "dead",
            "verus! { proof fn test(x: int) { if false { assert(x == x) by(bit_vector); } } }",
        ),
        (
            "pruned",
            "verus! { proof fn test(x: int) requires false, { assert(x == x) by(bit_vector); } }",
        ),
    ] {
        for disabled in [false, true] {
            let result = run(&format!("bv_{name}_identity_{disabled}"), source, disabled);
            assert_eq!(
                result.outcome(),
                if disabled { "refused" } else { "checked" },
                "{result:?}"
            );
        }
    }
    for (name, source) in [
        (
            "dead",
            "verus! { proof fn test() { if false { assert(false) by(bit_vector); } } }",
        ),
        (
            "pruned",
            "verus! { proof fn test() requires false, { assert(false) by(bit_vector); } }",
        ),
    ] {
        for disabled in [false, true] {
            let result = run(&format!("bv_{name}_false_{disabled}"), source, disabled);
            assert_eq!(result.outcome(), "verification-failed", "{result:?}");
            assert!(result
                .errors()
                .iter()
                .any(|error| error.message == "bitvector assertion not satisfied"));
        }
    }
}

#[test]
fn source_folding_preserves_prior_checks_and_distinct_local_versions() {
    for (name, source) in [
        (
            "checked_division",
            "verus! { fn test(x: u32, y: u32) { let z = x / y; assert(z == z) by(bit_vector); } }",
        ),
        (
            "changed_version",
            "verus! { proof fn test(x: u32, y: u32) { let old_x = x; let mut z = x; z = y; assert(old_x == z) by(bit_vector); } }",
        ),
    ] {
        for disabled in [false, true] {
            let result = run(&format!("bv_{name}_{disabled}"), source, disabled);
            assert_eq!(result.outcome(), "verification-failed", "{result:?}");
            assert!(!result.errors().is_empty(), "{result:?}");
        }
    }
}

#[test]
fn unconditional_return_discards_its_bv_suffix_before_finite_conversion() {
    for (name, source) in [
        (
            "false",
            "verus! { proof fn test() { return; assert(false) by(bit_vector); } }",
        ),
        (
            "unsupported",
            "verus! { proof fn test(x: int, y: int) { return; assert(x == y) by(bit_vector); } }",
        ),
    ] {
        for disabled in [false, true] {
            let accepted = run(&format!("bv_return_{name}_{disabled}"), source, disabled);
            assert_eq!(accepted.outcome(), "checked", "{accepted:?}");
            assert_eq!(accepted.exit, 0, "{accepted:?}");
            assert!(accepted.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["sites_proved"] == 0 && function["sites_failed"] == 0));
        }
    }
}
