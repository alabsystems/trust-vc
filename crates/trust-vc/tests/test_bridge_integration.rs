// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test proving the verification bridge connects all components.
//!
//! This test addresses issue #821 - THE critical connector.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::vc::ProofObligation;
use trust_vc_core::verification_bridge::{self, VerificationPipeline};
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

/// Test proving the full pipeline works: macro -> bridge -> VC -> ay -> result
#[test]
fn test_full_pipeline_integration() {
    common::with_clean_verification(|| {
        // Simulate what a proc macro would do - register obligations
        verification_bridge::register_proof(
            "integration_proof",
            vec![
                ProofObligation::assert("check1", "10 > 5"),
                ProofObligation::assert("check2", "5 + 5 == 10"),
                ProofObligation::assert("check3", "100 - 50 == 50"),
            ],
        );

        let pipeline = VerificationPipeline::collect_from_macros();

        assert_eq!(
            pipeline.context().obligations().len(),
            3,
            "Bridge should have collected all 3 registered obligations"
        );

        let result = pipeline.verify();

        assert_eq!(
            result,
            VerifyResult::Verified,
            "All assertions should verify through ay"
        );
    })
}

/// Test that the bridge catches invalid assertions
#[test]
fn test_bridge_catches_invalid() {
    common::with_clean_verification(|| {
        verification_bridge::register_proof(
            "invalid_proof",
            vec![
                ProofObligation::assert("invalid", "5 > 10"), // This is false
            ],
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Counterexample { .. } => {}
            VerifyResult::Verified => {
                panic!("Invalid assertion (5 > 10) should not verify!");
            }
            _ => panic!("Unexpected result: {:?}", result),
        }
    })
}

/// Test demonstrating how proc macros will use the bridge
/// (#1595: was asserting "true" and "42 == 42" — trivial tautologies)
/// Now uses a symbolic variable with assumption to require real solver reasoning.
#[test]
fn test_proc_macro_simulation() {
    common::with_clean_verification(|| {
        fn simulated_proof_expansion() {
            // Simulate proc macro declaring a symbolic variable and registering obligations
            verify_macro::collect_variable("n".to_string(), "i32".to_string());
            verification_bridge::register_proof(
                "my_proof_function",
                vec![
                    ProofObligation::assume("precondition", "n > 0 && n < 2147483647"),
                    ProofObligation::assert("line_10", "n + 1 > 1"),
                ],
            );
        }

        simulated_proof_expansion();

        let pipeline = VerificationPipeline::collect_from_macros();
        // 2 obligations: 1 assumption + 1 assertion
        assert_eq!(pipeline.context().obligations().len(), 2);

        let result = pipeline.verify();
        assert_eq!(result, VerifyResult::Verified);
    })
}

/// Test showing the bridge provides observability
#[test]
fn test_bridge_diagnostics() {
    common::with_clean_verification(|| {
        verification_bridge::register_proof(
            "diagnostic_test",
            vec![
                ProofObligation::assert("a1", "1 == 1"),
                ProofObligation::assert("a2", "2 == 2"),
            ],
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let diagnostic = pipeline.diagnose();

        assert_eq!(diagnostic.num_obligations(), 2);
        assert!(diagnostic.has_assertions());
        assert!(!diagnostic.has_assumptions());
    })
}

/// The acceptance test for issue #821
#[test]
fn test_issue_821_acceptance_criteria() {
    common::with_clean_verification(|| {
        verification_bridge::register_proof(
            "acceptance_test",
            vec![ProofObligation::assert("ac", "7 * 6 == 42")],
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert_eq!(result, VerifyResult::Verified);
    })
}
