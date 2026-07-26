// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for ghost! macro and ghost-related features
//!
//! These tests verify that incorrect ghost usage is properly rejected.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[test]
fn test_ghost_requires_false_without_ensures_is_error() {
    // A context with only requires (assumptions) and no ensures (assertions) is
    // rejected as a soundness error (#1859). There is nothing to prove.
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "ghost_requires_false".to_string(),
            "false".to_string(),
            Some("ghost_negative:ghost_requires_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "ghost_requires(false) with no ensures should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_ensures_violated() {
    // Test that violated ghost_ensures is caught
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_result".to_string(), "i32".to_string());

        // Ghost function returns 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_returns_5".to_string(),
            "ghost_result == 5".to_string(),
            Some("ghost_negative:ghost_ensures_violated".to_string()),
        );

        // But ghost_ensures claims result > 10
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ghost_ensures_gt_10".to_string(),
            "ghost_result > 10".to_string(),
            Some("ghost_negative:ghost_ensures_violated".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Violated ghost_ensures should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_assertion_false() {
    // Test that false assertions in ghost blocks are caught
    common::with_clean_verification(|| {
        // Ghost block with false assertion
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_assert_false".to_string(),
            "1 == 2".to_string(), // Obviously false
            Some("ghost_negative:ghost_assert_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "False assertion in ghost block should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_contradictory_assumptions() {
    // Test that contradictory ghost assumptions are caught.
    // With contradictory assumptions (x > 10 AND x < 5), any assertion is
    // vacuously Verified (ex falso quodlibet). This is standard SMT behavior.
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_x".to_string(), "i32".to_string());

        // First ghost assumption: x > 10
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_assume_x_gt_10".to_string(),
            "ghost_x > 10".to_string(),
            Some("ghost_negative:contradictory".to_string()),
        );

        // Second ghost assumption: x < 5 (contradicts first)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_assume_x_lt_5".to_string(),
            "ghost_x < 5".to_string(),
            Some("ghost_negative:contradictory".to_string()),
        );

        // Try to assert something based on these assumptions
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_assert_x_eq_7".to_string(),
            "ghost_x == 7".to_string(),
            Some("ghost_negative:contradictory".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Vacuous truth detection (#2258): contradictory assumptions are caught
        // before assertions run, returning Unknown instead of silently verifying.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Contradictory assumptions should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_division_by_zero() {
    // Test that division by zero in ghost code is caught
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_divisor".to_string(), "i32".to_string());

        // Set ghost divisor to 0
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_divisor_zero".to_string(),
            "ghost_divisor == 0".to_string(),
            Some("ghost_negative:div_by_zero".to_string()),
        );

        // Try to use division in ghost assertion
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_div_result".to_string(),
            "100 / ghost_divisor > 0".to_string(), // Division by zero!
            Some("ghost_negative:div_by_zero".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "Division by zero in ghost code should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_overflow() {
    // Test that overflow in ghost computations is detected
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_val".to_string(), "i32".to_string());

        // Set ghost value to i32::MAX
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_max".to_string(),
            "ghost_val == 2147483647".to_string(), // i32::MAX
            Some("ghost_negative:overflow".to_string()),
        );

        // Try to add 1 (would overflow)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_overflow".to_string(),
            "ghost_val + 1 > ghost_val".to_string(), // Overflow!
            Some("ghost_negative:overflow".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "Overflow in ghost computation should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_spec_mismatch() {
    // Test that ghost function not matching its spec is caught
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_input".to_string(), "i32".to_string());
        verify_macro::collect_variable("ghost_output".to_string(), "i32".to_string());

        // Ghost function spec says it doubles the input
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_input".to_string(),
            "ghost_input == 5".to_string(),
            Some("ghost_negative:spec_mismatch".to_string()),
        );

        // But implementation triples it
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_impl".to_string(),
            "ghost_output == ghost_input * 3".to_string(), // Triples, not doubles
            Some("ghost_negative:spec_mismatch".to_string()),
        );

        // Spec says output should be input * 2
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ghost_spec".to_string(),
            "ghost_output == ghost_input * 2".to_string(), // This will fail
            Some("ghost_negative:spec_mismatch".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Ghost function not matching spec should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_invariant_violated() {
    // Test that violated ghost invariants are caught
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_counter".to_string(), "i32".to_string());

        // Ghost invariant: counter >= 0
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_invariant".to_string(),
            "ghost_counter >= 0".to_string(),
            Some("ghost_negative:invariant".to_string()),
        );

        // But set counter to -1 (violates invariant)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_counter_negative".to_string(),
            "ghost_counter == -1".to_string(),
            Some("ghost_negative:invariant".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Violated ghost invariant should be caught, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_recursive_without_decreases() {
    // Test that ghost recursion without proper decreases is problematic
    common::with_clean_verification(|| {
        // Declare ghost variables used in obligations
        verify_macro::collect_variable("ghost_n".to_string(), "i32".to_string());

        // Ghost recursive function without decreases clause
        // This simulates infinite recursion
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ghost_recurse".to_string(),
            "ghost_n == ghost_n".to_string(), // No progress
            Some("ghost_negative:no_decreases".to_string()),
        );

        // Try to assert termination
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_terminates".to_string(),
            "ghost_n == 0".to_string(), // Can't prove this terminates
            Some("ghost_negative:no_decreases".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Without proper decreases, we can't prove termination
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Ghost recursion without decreases should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ghost_unreachable_code() {
    // Test that requires(false) makes assertions vacuously true
    common::with_clean_verification(|| {
        // Ghost requires false (makes code unreachable)
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "ghost_unreachable".to_string(),
            "false".to_string(),
            Some("ghost_negative:unreachable".to_string()),
        );

        // Try to prove something in unreachable context
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ghost_prove_anything".to_string(),
            "1 == 2".to_string(), // Vacuously true under false assumption
            Some("ghost_negative:unreachable".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Vacuous truth detection (#2258): requires(false) makes assumptions
        // contradictory → caught and reported as Unknown.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "requires(false) should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}
