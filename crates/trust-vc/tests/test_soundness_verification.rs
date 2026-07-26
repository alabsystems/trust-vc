// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct soundness verification tests
//!
//! These tests verify that the verifier correctly rejects false assertions.
//! If any of these tests fail, the verifier has a soundness bug.

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_verifier_rejects_literal_false() {
    common::with_clean_verification(|| {
        // Register a literal false assertion
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "literal_false".to_string(),
            "false".to_string(),
            Some("soundness_test:literal_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "SOUNDNESS BUG: Verifier accepted literal 'false' as true! Got: {:?}",
            result
        );
    })
}

#[test]
fn test_verifier_rejects_zero_greater_than_zero() {
    common::with_clean_verification(|| {
        // Register 0 > 0 which is clearly false
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "zero_gt_zero".to_string(),
            "0 > 0".to_string(),
            Some("soundness_test:zero_gt_zero".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "SOUNDNESS BUG: Verifier accepted '0 > 0' as true! Got: {:?}",
            result
        );
    })
}

#[test]
fn test_verifier_rejects_one_equals_two() {
    common::with_clean_verification(|| {
        // Register 1 == 2 which is clearly false
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "one_eq_two".to_string(),
            "1 == 2".to_string(),
            Some("soundness_test:one_eq_two".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "SOUNDNESS BUG: Verifier accepted '1 == 2' as true! Got: {:?}",
            result
        );
    })
}

#[test]
fn test_verifier_accepts_literal_true() {
    common::with_clean_verification(|| {
        // Register a literal true assertion - should verify
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "literal_true".to_string(),
            "true".to_string(),
            Some("soundness_test:literal_true".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Verifier should accept literal 'true', got: {:?}",
            result
        );
    })
}

#[test]
fn test_verifier_accepts_one_equals_one() {
    common::with_clean_verification(|| {
        // Register 1 == 1 which is true
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "one_eq_one".to_string(),
            "1 == 1".to_string(),
            Some("soundness_test:one_eq_one".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Verifier should accept '1 == 1', got: {:?}",
            result
        );
    })
}
