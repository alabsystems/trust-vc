// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Debug test for measure non-negative issue

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_measure_nonnegative_debug() {
    common::with_clean_verification(|| {
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

        let pipeline = VerificationPipeline::collect_from_macros();

        // Debug: Check what obligations were collected
        let diag = pipeline.diagnose();
        eprintln!("DEBUG: Pipeline diagnostic: {:?}", diag);
        eprintln!("DEBUG: Context: {:?}", pipeline.context());

        let result = pipeline.verify();
        eprintln!("DEBUG: Verify result: {:?}", result);

        // The first assertion (n == -5 for unconstrained n) has NOT(n == -5)
        // which is SAT (e.g., n = 0), so ay returns Counterexample immediately.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Assertion n == -5 for unconstrained n should produce counterexample, got: {:?}",
            result
        );
    })
}
