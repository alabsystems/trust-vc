// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests using the real verification pipeline
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_pipeline_verifies_true() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Collect assertion: assert!(true)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "assert!(true) should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_rejects_false() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Collect assertion: assert!(false)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "false".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "assert!(false) should fail verification, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_handles_variables() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Declare variable x: i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Collect assertion: assert!(x + 0 == x)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "x + 0 == x".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "x + 0 == x should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_handles_complex_assertions() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Declare variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Collect precondition: requires!(x > 0)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Requires,
            "precondition".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Add overflow prevention: x and y must be reasonable values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "overflow_prevention_x".to_string(),
            "x < 1000000000".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "overflow_prevention_y".to_string(),
            "y < 1000000000".to_string(),
            None,
        );

        // Collect assertion: assert!(x + y > y)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "x + y > y".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 implies x + y > y should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_preconditions_matter() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // WITHOUT precondition, x > 0 cannot be verified
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "x > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "x > 0 without precondition should fail, got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_postconditions() {
    common::with_clean_verification(|| {
        // Clear any previous state
        // Function: fn abs(x: i32) -> i32
        // requires!(true)
        // ensures!(result >= 0)

        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Postcondition: result >= 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "postcondition".to_string(),
            "result >= 0".to_string(),
            None,
        );

        // Implementation would assign result = if x >= 0 { x } else { -x }
        // For test, we just verify the postcondition is collected

        let pipeline = VerificationPipeline::collect_from_macros();

        // Check that postcondition was collected
        assert!(
            !pipeline.context().obligations().is_empty(),
            "Postcondition should be collected"
        );

        // Actually verify — result >= 0 cannot be proven without constraints on result,
        // so this should NOT verify (it should produce a counterexample)
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Unbounded ensures!(result >= 0) should fail without assumptions, got {:?}",
            result
        );
    })
}
