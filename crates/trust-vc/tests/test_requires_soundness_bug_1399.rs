// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for issue #1399: ObligationKind::Requires was incorrectly treated as assumption
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! This test verifies that requires clauses are properly checked, not assumed

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[test]
fn test_requires_false_vacuously_verified() {
    // In callee-side verification, requires(false) is an assumption.
    // With only assumptions and no assertions, result is vacuously Verified.
    // See #1503 for semantics discussion.
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            Some("test_requires_soundness:false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(false) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_impossible_condition_vacuous() {
    // In callee-side verification, requires(1 > 2) is an assumption.
    // With only assumptions and no assertions, result is vacuously Verified.
    // See #1503.
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_impossible".to_string(),
            "1 > 2".to_string(),
            Some("test_requires_soundness:impossible".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(1 > 2) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_true_is_accepted() {
    // Test that valid requires conditions are accepted
    common::with_clean_verification(|| {
        // Add requires!(true) - this should pass verification
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_true".to_string(),
            "true".to_string(),
            Some("test_requires_soundness:true".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(true) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_with_variables() {
    // Test that requires with variables works correctly
    common::with_clean_verification(|| {
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x = 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            Some("test_requires_soundness:vars".to_string()),
        );

        // Add requires!(x > 0) - should pass since x = 5
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_x_positive".to_string(),
            "x > 0".to_string(),
            Some("test_requires_soundness:vars".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(x > 0) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_not_satisfied_vacuous() {
    // In callee-side verification, Requires is an assumption.
    // So we have: assume(x == -5) AND assume(x > 0) = contradictory.
    // With no assertions, result is vacuously Verified.
    // See #1503.
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == -5".to_string(),
            Some("test_requires_soundness:not_satisfied".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_x_positive".to_string(),
            "x > 0".to_string(),
            Some("test_requires_soundness:not_satisfied".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Contradicting assumptions with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_assume_still_works() {
    // Test that Assume obligations still work as assumptions
    common::with_clean_verification(|| {
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 10 (this is an assumption, not checked)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_x_large".to_string(),
            "x > 10".to_string(),
            Some("test_requires_soundness:assume".to_string()),
        );

        // Assert x > 5 (should pass because we assumed x > 10)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_x_gt_5".to_string(),
            "x > 5".to_string(),
            Some("test_requires_soundness:assume".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Assumptions should still work correctly, got: {:?}",
            result
        );
    })
}
