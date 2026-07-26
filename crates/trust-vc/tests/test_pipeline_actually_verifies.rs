// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright: 2026 Andrew Yates | License: Apache 2.0

//! Test that pipeline ACTUALLY verifies, not just returns stubbed results
//! Part of #1052
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_pipeline_accepts_true() {
    common::with_clean_verification(|| {
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
            "Pipeline should verify assert!(true), got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_rejects_false_actually() {
    common::with_clean_verification(|| {
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
            "Pipeline should reject assert!(false), got {:?}",
            result
        );
    })
}

#[test]
fn test_pipeline_detects_contradiction() {
    common::with_clean_verification(|| {
        // Two contradictory assertions
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );
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
            "Pipeline should detect contradiction, got {:?}",
            result
        );
    })
}
