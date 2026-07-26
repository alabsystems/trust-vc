// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test for the critical u64 >= 0 case
// This should always verify for unsigned types

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_u64_ge_zero_should_verify() {
    common::with_clean_verification(|| {
        // Declare a u64 variable
        verify_macro::collect_variable("x".to_string(), "u64".to_string());

        // Assert that x >= 0 (should always be true for unsigned)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "u64_nonneg".to_string(),
            "x >= 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Verified => {
                // This is what we expect
            }
            VerifyResult::Counterexample {
                obligation_name,
                model,
                ..
            } => {
                panic!(
                    "BUG: u64 >= 0 found counterexample! Obligation: {}, Model: {:?}",
                    obligation_name, model
                );
            }
            _ => {
                panic!("Unexpected result: {:?}", result);
            }
        }
    })
}

#[test]
fn test_u32_gt_zero_with_nonzero_value() {
    common::with_clean_verification(|| {
        // Declare a u32 variable
        verify_macro::collect_variable("y".to_string(), "u32".to_string());

        // Assume y equals u32::MAX
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_max".to_string(),
            "y == 4294967295".to_string(), // u32::MAX
            None,
        );

        // Assert that y > 0 (should be true since y = u32::MAX)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "u32_positive".to_string(),
            "y > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Verified => {
                // This is what we expect
            }
            VerifyResult::Counterexample {
                obligation_name,
                model,
                ..
            } => {
                panic!(
                    "BUG: u32::MAX > 0 found counterexample! Obligation: {}, Model: {:?}",
                    obligation_name, model
                );
            }
            _ => {
                panic!("Unexpected result: {:?}", result);
            }
        }
    })
}
