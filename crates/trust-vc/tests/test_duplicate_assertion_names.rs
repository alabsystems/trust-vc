// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for duplicate assertion name handling
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_multiple_same_assertions() {
    common::with_clean_verification(|| {
        // Multiple assert!(true) statements
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "assertion".to_string(),
            "true".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should still verify even with duplicate assertions
        assert!(
            matches!(result, VerifyResult::Verified),
            "Multiple true assertions should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_mixed_duplicate_assertions() {
    common::with_clean_verification(|| {
        // Mix of multiple true and false assertions
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

        // Should fail because of false assertions
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Mixed assertions with false should fail, got: {:?}",
            result
        );
    })
}
