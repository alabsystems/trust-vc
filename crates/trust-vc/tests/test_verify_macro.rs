// Test for ONE real verification that actually works
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! This test demonstrates ONE working end-to-end verification
//! using the REAL system (not a fake pipeline).
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

mod common;

#[test]
fn test_one_real_verification() {
    common::with_clean_verification(|| {
        // Add assertion
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "test".to_string(),
            "true".to_string(),
            None,
        );

        // Use REAL pipeline
        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should verify
        assert!(matches!(result, trust_vc_core::VerifyResult::Verified));
    })
}
