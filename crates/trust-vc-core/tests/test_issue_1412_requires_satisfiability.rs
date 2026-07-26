// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for issue #1412: Requires clauses with unsatisfiable conditions like "1 > 2"
//! should be detected as counterexamples, not just literal "false"
//!
//! The current fix only handles literal "false" and "0 > 0", but other
//! unsatisfiable conditions are not caught.

mod common;

use trust_vc_core::vc::{ObligationKind, VerificationMode};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[test]
fn test_requires_1_gt_2_is_unsatisfiable() {
    // Test that requires!(1 > 2) is detected as unsatisfiable
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_1_gt_2".to_string(),
            "1 > 2".to_string(),
            Some("test:1".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "BUG #1412: requires!(1 > 2) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_false_and_true_is_unsatisfiable() {
    // Test that requires!(false && true) is detected as unsatisfiable
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false_and_true".to_string(),
            "false && true".to_string(),
            Some("test:2".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "BUG #1412: requires!(false && true) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_5_lt_3_is_unsatisfiable() {
    // Test that requires!(5 < 3) is detected as unsatisfiable
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_5_lt_3".to_string(),
            "5 < 3".to_string(),
            Some("test:3".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "BUG #1412: requires!(5 < 3) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_complex_unsatisfiable_expression() {
    // Test that complex unsatisfiable expressions are detected
    common::with_clean_verification(|| {
        // Declare a variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Add an impossible requires: x > 10 && x < 5
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_impossible_range".to_string(),
            "x > 10 && x < 5".to_string(),
            Some("test:4".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "BUG #1412: requires!(x > 10 && x < 5) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_false_still_works() {
    // Test that the existing fix for literal "false" still works
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            Some("test:5".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "requires!(false) should still produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_true_still_verifies() {
    // Test that satisfiable requires still verify correctly
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_true".to_string(),
            "true".to_string(),
            Some("test:6".to_string()),
        );

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "requires!(true) should verify, got: {:?}",
            result
        );
    })
}
