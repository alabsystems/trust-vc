// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test that the pipeline can handle complex expressions, not just literals.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_pipeline_handles_arithmetic_expressions() {
    common::with_clean_verification(|| {
        // Test: assert!(1 + 1 == 2)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "1 + 1 == 2".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Pipeline should be able to verify simple arithmetic: {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_handles_variable_expressions() {
    common::with_clean_verification(|| {
        // Declare variable x: i32
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Precondition: x > 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "precondition".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Assertion: x >= 1
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "x >= 1".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Pipeline should handle variable assertions with preconditions: {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_handles_complex_boolean_logic() {
    common::with_clean_verification(|| {
        // Declare variables
        verify_macro::collect_variable("a".to_string(), "bool".to_string());
        verify_macro::collect_variable("b".to_string(), "bool".to_string());

        // Precondition: a || b
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "precondition".to_string(),
            "a || b".to_string(),
            None,
        );

        // Assertion: a || b || false
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "a || b || false".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Pipeline should handle complex boolean logic: {:?}",
            result
        );
    })
}
