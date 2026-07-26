// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Debug test to understand the soundness bug
//!
//! VERIFICATION LEVEL: SOUNDNESS

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_contradictory_assertions_should_fail() {
    common::with_clean_verification(|| {
        // Test that directly contradictory assertions produce a counterexample
        // Declare a variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Add two contradictory assertions
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_is_positive".to_string(),
            "x > 0".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_is_negative".to_string(),
            "x < 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        eprintln!("DEBUG: result = {:?}", result);

        // x > 0 cannot hold for all i32 values (x = 0 is counterexample).
        // The first assertion checked should produce Counterexample.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Contradictory assertions (x > 0 AND x < 0) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_simple_false_assertion() {
    common::with_clean_verification(|| {
        // Test that a simple false assertion produces a counterexample
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_assertion".to_string(),
            "5 > 10".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // 5 > 10 is decidably false — NOT(5 > 10) is trivially SAT.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "False assertion (5 > 10) should produce counterexample, got: {:?}",
            result
        );
    })
}
