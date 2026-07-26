// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Edge case tests for the verification pipeline
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_pipeline_handles_empty_context() {
    common::with_clean_verification(|| {
        // No obligations collected
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Empty context correctly returns an error to prevent vacuous proofs
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Empty context should return error (not vacuously verify), got: {:?}",
            result
        );

        // Verify the error mentions empty context
        if let VerifyResult::Error { message } = result {
            assert!(
                message.contains("empty context"),
                "Error should mention empty context, got: {}",
                message
            );
        }
    })
}

#[test]
fn test_pipeline_handles_only_variables() {
    common::with_clean_verification(|| {
        // Only declare variables, no assertions
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "bool".to_string());

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Variables without obligations correctly returns an error (no proof obligations to check)
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Variables without assertions should return error (no obligations), got {:?}",
            result
        );

        // Verify the error mentions empty context or no obligations
        if let VerifyResult::Error { message } = result {
            assert!(
                message.contains("empty context") || message.contains("no obligations"),
                "Error should mention empty context or no obligations, got: {}",
                message
            );
        }
    })
}

#[test]
fn test_pipeline_handles_multiple_assertions() {
    common::with_clean_verification(|| {
        // Multiple consistent assertions
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "1 == 1".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "2 > 1".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Multiple true assertions should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_handles_preconditions_and_postconditions() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Precondition: x >= 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Requires,
            "precondition".to_string(),
            "x >= 0".to_string(),
            None,
        );

        // Postcondition: result >= 0 (for abs function)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "postcondition".to_string(),
            "result >= 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();

        // Check that both obligations were collected
        assert_eq!(
            pipeline.context().obligations().len(),
            2,
            "Should have collected both pre and postcondition"
        );
    })
}

#[test]
fn test_pipeline_handles_loop_invariants() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("i".to_string(), "usize".to_string());
        verify_macro::collect_variable("n".to_string(), "usize".to_string());

        // Loop invariant: i <= n
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert, // Loop invariants are asserted at each iteration
            "loop_invariant".to_string(),
            "i <= n".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();

        assert!(
            !pipeline.context().obligations().is_empty(),
            "Should have collected loop invariant"
        );
    })
}
