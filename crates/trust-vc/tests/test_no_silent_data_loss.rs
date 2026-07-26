// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test verification context behavior
// Verifies fix for #572 - ensuring proper error handling for verification data collection

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};

mod common;

#[test]
fn test_basic_obligation_collection() {
    common::with_clean_verification(|| {
        // Collect an obligation - this should work in normal cases
        collect_obligation(
            ObligationKind::Assert,
            "test_assert".to_string(),
            "true".to_string(),
            Some("test.rs:1".to_string()),
        );

        // Verify it was collected properly
        let result = verify_collected();
        assert!(matches!(result, trust_vc_core::VerifyResult::Verified));
    })
}

#[test]
fn test_variable_collection() {
    common::with_clean_verification(|| {
        // Collect a variable declaration
        collect_variable("x".to_string(), "i32".to_string());

        // Collect an obligation using that variable
        collect_obligation(
            ObligationKind::Assert,
            "test_with_var".to_string(),
            "x > 0".to_string(),
            Some("test.rs:1".to_string()),
        );

        // Verify the collected context — x > 0 is not always true (x = 0 is
        // counterexample), so this should produce Counterexample.
        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Counterexample { .. }),
            "x > 0 for unconstrained i32 should produce counterexample, got: {:?}",
            result
        );
    })
}
