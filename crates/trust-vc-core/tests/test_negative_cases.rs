// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Comprehensive negative test cases for verification features
//!
//! This file tests that invalid proofs, unsatisfiable conditions, and incorrect
//! code properly FAIL verification. These tests ensure our verification system
//! doesn't have false positives (accepting invalid code).

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable};
use trust_vc_core::VerifyResult;

#[test]
fn test_invalid_ensures_fails() {
    // Test that ensures!(false) fails verification
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Ensures,
            "invalid_ensures".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures!(false) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_assert_fails() {
    // Test that assert!(1 > 2) fails verification
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Assert,
            "invalid_assert".to_string(),
            "1 > 2".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "assert!(1 > 2) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsatisfiable_requires_vacuously_true() {
    // An unsatisfiable requires combined with an assertion is vacuously Verified
    // (ex falso quodlibet: false implies anything).
    // requires(false) as an assumption makes SAT(false AND NOT(assertion)) = UNSAT
    // for ANY assertion, so all assertions pass vacuously.
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Requires,
            "unsatisfiable_requires".to_string(),
            "0 > 1".to_string(),
            Some("test:3:1".to_string()),
        );

        // Add an assertion that is normally false — under unsatisfiable requires
        // it becomes vacuously true (ex falso quodlibet).
        collect_obligation(
            ObligationKind::Assert,
            "vacuous_assert".to_string(),
            "1 == 2".to_string(),
            Some("test:4:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Vacuous truth detection (#2258): requires(0 > 1) is false,
        // making assumptions contradictory → caught as Unknown.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Unsatisfiable requires should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_non_terminating_measure_fails() {
    // Test that increasing measures fail termination checking
    common::with_clean_verification(|| {
        collect_variable("n".to_string(), "u64".to_string());

        // Assume n is bounded to avoid overflow
        // Note: Use a value that fits in i64 due to encoder limitation
        collect_obligation(
            ObligationKind::Assume,
            "n_bounded".to_string(),
            "n < 9223372036854775807".to_string(), // i64::MAX
            None,
        );

        // Invalid: measure increases
        collect_obligation(
            ObligationKind::MeasureDecreases,
            "increasing_measure".to_string(),
            "(n + 1) < n".to_string(), // This is false!
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Increasing measure should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_violated_postcondition_fails() {
    // Test that violated postconditions fail
    common::with_clean_verification(|| {
        collect_variable("i".to_string(), "u32".to_string());

        // Assume i starts at 0
        collect_obligation(
            ObligationKind::Assume,
            "i_start".to_string(),
            "i == 0".to_string(),
            None,
        );

        // Invalid postcondition: i is negative (but u32 can't be negative!)
        collect_obligation(
            ObligationKind::Ensures,
            "invalid_postcondition".to_string(),
            "i < 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Violated postcondition should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_overflow_condition_fails() {
    // Test that overflow conditions are caught
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "u8".to_string());

        // Assume x is at max value
        collect_obligation(
            ObligationKind::Assume,
            "x_max".to_string(),
            "x == 255".to_string(),
            None,
        );

        // Try to assert x + 1 > x (would overflow!)
        // Note: In actual verification, overflow should be detected
        collect_obligation(
            ObligationKind::Assert,
            "overflow_check".to_string(),
            "x + 1 > x".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Overflow should either produce counterexample or error
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }
            ),
            "Overflow condition should fail verification, got: {:?}",
            result
        );
    })
}

#[test]
fn test_contradictory_assertions_fail() {
    // Test that contradictory assertions are detected
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        // Assert x > 10
        collect_obligation(
            ObligationKind::Assert,
            "x_gt_10".to_string(),
            "x > 10".to_string(),
            None,
        );

        // Also assert x < 5 (contradiction!)
        collect_obligation(
            ObligationKind::Assert,
            "x_lt_5".to_string(),
            "x < 5".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Contradictory assertions should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_array_access_fails() {
    // Test that invalid array bounds check fails
    // Note: The encoder doesn't support arr.len() syntax directly,
    // so we use a separate length variable
    common::with_clean_verification(|| {
        collect_variable("arr_len".to_string(), "u32".to_string());
        collect_variable("idx".to_string(), "u32".to_string());

        // Assume array has length 5
        collect_obligation(
            ObligationKind::Assume,
            "len_is_5".to_string(),
            "arr_len == 5".to_string(),
            None,
        );

        // Try to assert that index 10 is valid (out of bounds!)
        collect_obligation(
            ObligationKind::Assert,
            "invalid_access".to_string(),
            "10 < arr_len".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Out-of-bounds access should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_division_by_zero_fails() {
    // Test that division by zero is caught
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());
        collect_variable("y".to_string(), "i32".to_string());

        // Set y to 0
        collect_obligation(
            ObligationKind::Assume,
            "y_zero".to_string(),
            "y == 0".to_string(),
            None,
        );

        // Try to assert something about x / y (division by zero!)
        collect_obligation(
            ObligationKind::Assert,
            "div_by_zero".to_string(),
            "x / y == 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Division by zero should produce error or counterexample
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }
            ),
            "Division by zero should fail verification, got: {:?}",
            result
        );
    })
}

#[test]
fn test_negative_measure_fails() {
    // Test that negative termination measures fail
    common::with_clean_verification(|| {
        collect_variable("n".to_string(), "i32".to_string());

        // Set n to negative value
        collect_obligation(
            ObligationKind::Assume,
            "n_negative".to_string(),
            "n == -5".to_string(),
            None,
        );

        // Check measure is non-negative (should fail!)
        collect_obligation(
            ObligationKind::MeasureNonNegative,
            "negative_measure".to_string(),
            "n >= 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Negative measure should produce counterexample, got: {:?}",
            result
        );
    })
}

/// Malformed expressions panic at collection time per #1723 invariant.
/// Expressions come from stringify!() and are always valid Rust syntax.
#[test]
fn test_malformed_expression_panics() {
    trust_vc_core::verify_macro::clear_all_thread_locals();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        collect_obligation(
            ObligationKind::Assert,
            "malformed".to_string(),
            "((1 + 2) * 3".to_string(), // Missing closing paren — invalid Rust syntax
            None,
        );
    }));

    trust_vc_core::verify_macro::clear_all_thread_locals();

    assert!(
        result.is_err(),
        "Malformed expression should panic per #1723"
    );
    let err = result.unwrap_err();
    let msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .unwrap_or("");
    assert!(
        msg.contains("#1723"),
        "Panic should reference #1723, got: {}",
        msg
    );
}

#[test]
fn test_undefined_variable_errors() {
    // Test that using undefined variables produces errors
    common::with_clean_verification(|| {
        // Use variable without declaring it
        collect_obligation(
            ObligationKind::Assert,
            "undefined_var".to_string(),
            "undefined_x > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Undefined variable should produce error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_type_mismatch_returns_error() {
    // Type mismatches should return a non-panic result with sort mismatch info (#1488)
    // Since W1-733 (#2216), sort mismatches degrade to Unknown (not Error) because
    // the encoder cannot distinguish user type errors from unsupported encoding patterns.
    common::with_clean_verification(|| {
        collect_variable("b".to_string(), "bool".to_string());
        collect_variable("n".to_string(), "i32".to_string());

        // Try to compare bool with integer (type error!)
        collect_obligation(
            ObligationKind::Assert,
            "type_mismatch".to_string(),
            "b > n".to_string(), // Can't compare bool and i32
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        // Sort mismatches now degrade to Unknown with a descriptive reason
        let reason = match &result {
            VerifyResult::Unknown { reason, .. } => reason.clone(),
            VerifyResult::Error { message } => message.clone(),
            other => panic!(
                "Type mismatch should return Unknown or Error, got: {:?}",
                other
            ),
        };
        assert!(
            reason.contains("sort mismatch") || reason.contains("Sort mismatch"),
            "Result message should mention sort mismatch, got: {}",
            reason
        );
    })
}

#[test]
fn test_type_mismatch_in_assumption_returns_error() {
    // Sort mismatch in assumption path should return a non-panic result (#1488)
    // Since W1-733 (#2216), sort mismatches degrade to Unknown across all paths.
    common::with_clean_verification(|| {
        collect_variable("flag".to_string(), "bool".to_string());
        collect_variable("count".to_string(), "i32".to_string());

        // Type mismatch in assumption (different code path than assertion)
        collect_obligation(
            ObligationKind::Assume,
            "bad_assume".to_string(),
            "flag > count".to_string(), // bool vs i32 mismatch
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "placeholder".to_string(),
            "count > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        let reason = match &result {
            VerifyResult::Unknown { reason, .. } => reason.clone(),
            VerifyResult::Error { message } => message.clone(),
            other => panic!(
                "Type mismatch in assumption should return Unknown or Error, got: {:?}",
                other
            ),
        };
        assert!(
            reason.contains("sort mismatch") || reason.contains("Sort mismatch"),
            "Result message should mention sort mismatch, got: {}",
            reason
        );
    })
}

#[test]
fn test_complex_false_condition_fails() {
    // Test complex conditions that evaluate to false
    common::with_clean_verification(|| {
        collect_variable("a".to_string(), "i32".to_string());
        collect_variable("b".to_string(), "i32".to_string());
        collect_variable("c".to_string(), "i32".to_string());

        // Set up values
        collect_obligation(
            ObligationKind::Assume,
            "a_val".to_string(),
            "a == 5".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "b_val".to_string(),
            "b == 10".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "c_val".to_string(),
            "c == 15".to_string(),
            None,
        );

        // Complex false condition: (a + b) > c && (b - a) > c
        // (5 + 10) > 15 is false, and (10 - 5) > 15 is false
        collect_obligation(
            ObligationKind::Assert,
            "complex_false".to_string(),
            "(a + b) > c && (b - a) > c".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Complex false condition should produce counterexample, got: {:?}",
            result
        );
    })
}
