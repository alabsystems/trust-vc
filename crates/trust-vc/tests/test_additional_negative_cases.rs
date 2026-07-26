// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Additional negative tests for verification features.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid conditions
//!
//! These tests cover edge cases and additional negative scenarios not covered
//! in other test files.

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_assert_with_undefined_variable_fails() {
    common::with_clean_verification(|| {
        // Test that assertions with undefined variables fail
        // Try to assert something about an undefined variable
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "undefined_var_assert".to_string(),
            "undefined_x > 0".to_string(), // undefined_x is not declared
            Some("test_additional_negative:undefined_variable".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(
                result,
                VerifyResult::Error { .. } | VerifyResult::Counterexample { .. }
            ),
            "Assertion with undefined variable should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_integer_overflow_assertion() {
    common::with_clean_verification(|| {
        // Test assertions about integer overflow
        // Declare a variable at max value
        verify_macro::collect_variable("x".to_string(), "u8".to_string());

        // Assume x is at max value
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_at_max".to_string(),
            "x == 255".to_string(),
            Some("test_additional_negative:overflow".to_string()),
        );

        // Assert that x + 1 > x (which would overflow)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "overflow_assert".to_string(),
            "x + 1 > x".to_string(), // This overflows for u8 at 255
            Some("test_additional_negative:overflow".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Overflow should cause verification failure
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Integer overflow assertion should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multiple_false_assertions() {
    common::with_clean_verification(|| {
        // Test multiple false assertions in same context
        // Add multiple false assertions
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_1".to_string(),
            "1 > 2".to_string(),
            Some("test_additional_negative:multiple_false".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_2".to_string(),
            "3 == 4".to_string(),
            Some("test_additional_negative:multiple_false".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_3".to_string(),
            "true == false".to_string(),
            Some("test_additional_negative:multiple_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Multiple false assertions should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_type_mismatch_in_comparison() {
    common::with_clean_verification(|| {
        // Test that type mismatches are caught
        // Declare variables of different types
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "bool".to_string());

        // Try to compare incompatible types
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "type_mismatch".to_string(),
            "x == y".to_string(), // Can't compare i32 to bool
            Some("test_additional_negative:type_mismatch".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // ay sort-mismatch panic is caught and wrapped as Unknown
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Type mismatch should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_nested_quantifier_contradiction() {
    // Verus-style quantifier syntax is not valid Rust; collect_obligation panics
    // at translate_rust_to_smt with unreachable!() (#1723)
    let result = std::panic::catch_unwind(|| {
        common::with_clean_verification(|| {
            verify_macro::collect_variable("arr".to_string(), "[i32]".to_string());
            verify_macro::collect_obligation(
                ObligationKind::Assert,
                "nested_contradiction".to_string(),
                "(forall i: i32 :: (exists x: i32 :: arr[i] == x && x > 0 && x < 0))".to_string(),
                Some("test_additional_negative:nested_quantifier".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let _result = pipeline.verify();
        })
    });
    // Verus quantifier syntax causes panic — this documents the gap
    assert!(
        result.is_err(),
        "Verus-style quantifier syntax should cause panic (not valid Rust), got Ok"
    );
}

#[test]
fn test_circular_ensures_dependency() {
    common::with_clean_verification(|| {
        // Test circular dependency in ensures clauses
        // Declare result variables
        verify_macro::collect_variable("result_a".to_string(), "i32".to_string());
        verify_macro::collect_variable("result_b".to_string(), "i32".to_string());

        // Create circular ensures dependencies
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_a".to_string(),
            "result_a == result_b + 1".to_string(),
            Some("test_additional_negative:circular_ensures".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_b".to_string(),
            "result_b == result_a + 1".to_string(), // Circular: a = b+1 and b = a+1
            Some("test_additional_negative:circular_ensures".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Circular dependency should make this unsatisfiable
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Circular ensures dependency should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_measure_increases() {
    common::with_clean_verification(|| {
        // Test that increasing measure is rejected
        // Declare measure variables
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_variable("n_next".to_string(), "u64".to_string());

        // Set up increasing measure
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "measure_start".to_string(),
            "n == 5".to_string(),
            Some("test_additional_negative:increasing_measure".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "measure_next".to_string(),
            "n_next == n + 1".to_string(), // Measure increases!
            Some("test_additional_negative:increasing_measure".to_string()),
        );

        // Assert that measure decreases (should fail)
        verify_macro::collect_obligation(
            ObligationKind::MeasureDecreases,
            "decreases_check".to_string(),
            "n_next < n".to_string(), // This is false since n_next = n + 1
            Some("test_additional_negative:increasing_measure".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Increasing measure should be rejected, got: {:?}",
            result
        );
    })
}
