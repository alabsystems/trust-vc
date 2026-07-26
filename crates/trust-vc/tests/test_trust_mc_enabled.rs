// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test to verify trust_mc feature flag configuration AND actual verification
//!
//! The trust_mc feature is used to disable verification when running with the trust_mc tool.
//! It should NOT be enabled by default - verification runs through test mode instead.
//!
//! Issue #908: Test files must actually invoke ay verification
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::vc::{ObligationKind, ProofObligation};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_trust_mc_feature_not_enabled_by_default() {
    common::with_clean_verification(|| {
        // Verify that trust_mc feature is NOT enabled by default
        // This is correct - verification happens through test mode, not trust_mc feature
        #[cfg(trust_mc)]
        {
            panic!(
                "trust_mc feature should NOT be enabled by default! It's only for trust_mc tool integration."
            );
        }

        #[cfg(not(trust_mc))]
        {
            // Good - trust_mc feature is not enabled, verification runs through test mode
            // CRITICAL FIX #908: Actually test verification works
            let mut pipeline = VerificationPipeline::new();

            // Add a simple assertion that should verify
            pipeline.add_obligation(ProofObligation::new(
                "trust_mc_test",
                "true",
                ObligationKind::Assert,
            ));

            let result = pipeline.verify();
            assert_eq!(
                result,
                VerifyResult::Verified,
                "Simple assertion should verify when trust_mc feature is off"
            );
        }
    })
}

#[test]
fn test_verification_runs_in_test_mode() {
    common::with_clean_verification(|| {
        // Verify that verification code is available in test mode
        // This works regardless of trust_mc feature
        #[cfg(test)]
        {
            // In test mode, verification functions are available
            // CRITICAL FIX #908: Actually run verification in test mode
            let mut pipeline = VerificationPipeline::new();

            // Add a non-trivial assertion that tests arithmetic
            pipeline.add_obligation(ProofObligation::new(
                "test_mode_verification",
                "(5 + 3) == 8",
                ObligationKind::Assert,
            ));

            let result = pipeline.verify();
            assert_eq!(
                result,
                VerifyResult::Verified,
                "Arithmetic assertion should verify in test mode"
            );
        }

        #[cfg(not(test))]
        {
            panic!("This test should only run in test mode");
        }
    })
}

#[test]
fn test_verification_can_detect_failures() {
    common::with_clean_verification(|| {
        // CRITICAL FIX #908: Test that verification can actually fail invalid assertions
        let mut pipeline = VerificationPipeline::new();

        // Add an assertion that should fail
        pipeline.add_obligation(ProofObligation::new(
            "invalid_assertion",
            "false",
            ObligationKind::Assert,
        ));

        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Invalid assertion should NOT verify, got: {:?}",
            result
        );
    })
}
