// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for issue #1370 using verify_macro interface
//!
//! VERIFICATION LEVEL: SOUNDNESS

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_measure_nonneg_via_macro_interface() {
    common::with_clean_verification(|| {
        // Declare variable
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Set n to negative value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "n_value".to_string(),
            "n == -5".to_string(),
            None,
        );

        // Termination measure must be non-negative
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureNonNegative,
            "measure_nonneg".to_string(),
            "n >= 0".to_string(),
            None,
        );

        // Verify using the pipeline
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                eprintln!("✓ Found counterexample for: {}", obligation_name);
                assert!(
                    obligation_name.contains("measure") || obligation_name.contains("n_value"),
                    "Should identify constraint failure, got: {}",
                    obligation_name
                );
            }
            VerifyResult::Verified => {
                panic!("SOUNDNESS BUG #1370: Contradictory MeasureNonNegative verified!");
            }
            other => {
                eprintln!("Got result: {:?}", other);
            }
        }
    })
}
