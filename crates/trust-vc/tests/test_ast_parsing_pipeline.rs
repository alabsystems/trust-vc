// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that the pipeline can parse complex expressions using AST
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_ast_parsing_simple_assert() {
    common::with_clean_verification(|| {
        // Simple assert!(true)
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
            "Simple assert should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_ast_parsing_variable_expression() {
    common::with_clean_verification(|| {
        // Declare variable x with value 5
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Add assumption that x = 5
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_init".to_string(),
            "x == 5".to_string(),
            None,
        );

        // Assert x > 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "x > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "x = 5 implies x > 0 should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_ast_parsing_complex_expression() {
    common::with_clean_verification(|| {
        // Declare variables
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());

        // Add assumptions
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_init".to_string(),
            "a == 10".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_init".to_string(),
            "b == 20".to_string(),
            None,
        );

        // Assert complex expression
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "(a + b) * 2 > 50".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "(10 + 20) * 2 = 60 > 50 should verify, got {:?}",
            result
        );
    })
}
