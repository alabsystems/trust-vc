// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for contract features (requires, ensures, old)
//!
//! These tests verify that incorrect usage of contracts is properly rejected.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[test]
fn test_requires_false_without_ensures_is_error() {
    // A context with only requires (assumptions) and no ensures (assertions) is
    // rejected as a soundness error (#1859). There is nothing to prove — the
    // pipeline returns Error instead of vacuously Verified.
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            Some("contracts_negative:requires_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires!(false) with no ensures should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_false_rejected() {
    // Test that ensures!(false) is rejected
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_false".to_string(),
            "false".to_string(),
            Some("contracts_negative:ensures_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures!(false) should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_contradictory_rejected() {
    // Test that contradictory requires are rejected
    common::with_clean_verification(|| {
        // Declare variable x of type i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // x > 5
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_x_gt_5".to_string(),
            "x > 5".to_string(),
            Some("contracts_negative:contradictory".to_string()),
        );

        // x < 3 (contradicts x > 5)
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_x_lt_3".to_string(),
            "x < 3".to_string(),
            Some("contracts_negative:contradictory".to_string()),
        );

        // Try to assert something that depends on both
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_x_eq_4".to_string(),
            "x == 4".to_string(),
            Some("contracts_negative:contradictory".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Vacuous truth detection (#2258): contradictory requires (x > 5 AND x < 3)
        // are caught before assertions run, returning Unknown instead of silently
        // verifying via principle of explosion.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Contradictory requires should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_not_satisfied_rejected() {
    // Test that ensures not satisfied by function body is rejected
    common::with_clean_verification(|| {
        // Declare variable result of type i32
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Function returns 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "return_value".to_string(),
            "result == 5".to_string(),
            Some("contracts_negative:ensures_not_satisfied".to_string()),
        );

        // But ensures says result > 10
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_gt_10".to_string(),
            "result > 10".to_string(),
            Some("contracts_negative:ensures_not_satisfied".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Unsatisfied ensures should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_insufficient_rejected() {
    // Test that insufficient requires leads to verification failure
    common::with_clean_verification(|| {
        // Declare variable x of type i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Only require x > 0
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_x_positive".to_string(),
            "x > 0".to_string(),
            Some("contracts_negative:insufficient_requires".to_string()),
        );

        // But assert x > 10 (stronger than precondition)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_x_gt_10".to_string(),
            "x > 10".to_string(),
            Some("contracts_negative:insufficient_requires".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Assertion stronger than requires should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_old_without_initialization_rejected() {
    // Test that using old!() on uninitialized value is rejected
    common::with_clean_verification(|| {
        // Try to use old!(x) without defining x first
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_old_undefined".to_string(),
            "old_x > 0".to_string(), // old!(x) becomes old_x
            Some("contracts_negative:old_undefined".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // This should fail because old_x is undefined
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Using old!() on undefined value should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_weaker_than_requires_inconsistent() {
    // Test a case where ensures is inconsistent with requires
    common::with_clean_verification(|| {
        // Declare variables input and result of type i32
        verify_macro::collect_variable("input".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Require input > 100
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_input_large".to_string(),
            "input > 100".to_string(),
            Some("contracts_negative:inconsistent".to_string()),
        );

        // Function computes result = input / 2
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "compute_result".to_string(),
            "result == input / 2".to_string(),
            Some("contracts_negative:inconsistent".to_string()),
        );

        // Incorrectly ensure result < 10 (impossible if input > 100)
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_result_small".to_string(),
            "result < 10".to_string(),
            Some("contracts_negative:inconsistent".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Inconsistent ensures with requires should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multiple_ensures_contradiction() {
    // Test that contradictory ensures clauses are rejected
    common::with_clean_verification(|| {
        // Declare variable result of type i32
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // First ensures: result > 0
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_positive".to_string(),
            "result > 0".to_string(),
            Some("contracts_negative:contradictory_ensures".to_string()),
        );

        // Second ensures: result < 0 (contradicts first)
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_negative".to_string(),
            "result < 0".to_string(),
            Some("contracts_negative:contradictory_ensures".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Contradictory ensures should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_division_by_zero_in_requires() {
    // Test that division by zero in requires is handled properly
    common::with_clean_verification(|| {
        // Declare variables x and y of type i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Set y = 0
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_is_zero".to_string(),
            "y == 0".to_string(),
            Some("contracts_negative:div_by_zero".to_string()),
        );

        // Requires with division by y (which is 0)
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_div".to_string(),
            "x / y > 5".to_string(), // Division by zero!
            Some("contracts_negative:div_by_zero".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // A context with only assumptions (requires + assume) and no assertions
        // (ensures/assert/invariant) is rejected as a soundness error (#1859).
        // Division by zero semantics are moot — there is nothing to prove.
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Requires-only context (no ensures) should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_overflow_in_ensures() {
    // Test that overflow in ensures is detected
    common::with_clean_verification(|| {
        // Declare variable x of type i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Set x to max i32 value
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_max".to_string(),
            "x == 2147483647".to_string(), // i32::MAX
            Some("contracts_negative:overflow".to_string()),
        );

        // Ensures that would cause overflow
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_overflow".to_string(),
            "x + 1 > x".to_string(), // This would overflow
            Some("contracts_negative:overflow".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Overflow should be detected and fail verification
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Overflow in ensures should not verify, got: {:?}",
            result
        );
    })
}
