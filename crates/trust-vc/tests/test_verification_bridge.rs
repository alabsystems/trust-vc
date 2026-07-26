// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test the verification bridge - the connector between proc macros and ay.
//!
//! This addresses issue #821 - the missing bridge that connects all components.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline
//!
//! # Architecture Note
//!
//! `#[trust_vc::proof]` functions auto-verify internally via the bridge:
//!   1. save_context_guard() — fresh scope
//!   2. Execute body — obligations collected
//!   3. VerificationPipeline::collect_from_macros() + verify() — ay check
//!   4. restore() — restore outer context
//!   5. Panic on failure
//!
//! Because the proof function consumes and restores the context, external
//! calls to collect_from_macros() after a proof returns will find an empty
//! context. This is by design — each proof is self-contained. Tests should
//! verify that proof functions succeed/fail as expected, which proves the
//! bridge is working.

use trust_vc_core::vc::ProofObligation;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

/// Test that the bridge connects proc macro output to ay verification.
///
/// The bridge is invoked INSIDE the proof function (via auto-verify).
/// A successful proof function call proves the bridge worked: the proof's
/// assertions were collected, encoded to SMT, and verified by ay.
#[test]
fn test_bridge_connects_macros_to_ay() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn bridge_test_proof() {
            trust_vc::assert!(10 > 5);
            trust_vc::assert!(5 + 5 == 10);
        }

        // If this returns without panic, the bridge successfully:
        // 1. Collected the assertions from the proof body
        // 2. Passed them to VerificationPipeline
        // 3. Encoded to SMT via AYEncoder
        // 4. ay verified them as valid
        bridge_test_proof();
    })
}

/// Test the full pipeline: Rust -> Macro -> Bridge -> VC -> ay -> Result
#[test]
fn test_full_pipeline_end_to_end() {
    common::with_clean_verification(|| {
        // Step 1: Define a proof with trust_vc macros
        #[trust_vc::proof]
        fn full_pipeline_proof() {
            trust_vc::assume!(true);
            trust_vc::assert!(1 + 1 == 2);
            trust_vc::assert!(10 - 5 == 5);
        }

        // Steps 2-5: The proof function internally uses the bridge to
        // collect obligations, encode to SMT, invoke ay, and check result.
        // Success (no panic) = full pipeline working.
        full_pipeline_proof();
    })
}

/// Test that invalid proofs are caught through the bridge
///
/// With the bridge integration, #[proof] functions automatically verify
/// and panic when invalid assertions are found.
#[test]
#[should_panic(expected = "Proof verification")]
fn test_bridge_catches_invalid_proofs() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn invalid_bridge_proof() {
            trust_vc::assert!(5 > 10); // This is false
        }

        // The bridge verifies internally and panics on failure
        invalid_bridge_proof();
    })
}

/// Test explicit registration API
///
/// The register_proof() API allows manual obligation registration
/// without going through proc macros. This is useful for testing
/// and for future macro implementations.
#[test]
fn test_explicit_registration() {
    common::with_clean_verification(|| {
        // Manually register obligations (simulating what a proc macro would do)
        trust_vc_core::verification_bridge::register_proof(
            "manual_proof",
            vec![
                ProofObligation::assert("check1", "7 > 3"),
                ProofObligation::assert("check2", "3 * 3 == 9"),
            ],
        );

        // Collect and verify
        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(pipeline.context().obligations().len(), 2);

        let result = pipeline.verify();
        assert_eq!(result, VerifyResult::Verified);
    })
}

/// Test pipeline diagnostics for debugging
///
/// Uses the explicit registration API to test diagnostic output
/// since proof functions auto-verify and clean up their context.
#[test]
fn test_pipeline_diagnostics() {
    common::with_clean_verification(|| {
        // Build a pipeline manually to test diagnostics
        let mut pipeline = VerificationPipeline::new();
        pipeline.add_obligation(ProofObligation::assume("test_assume", "true"));
        pipeline.add_obligation(ProofObligation::assert("test_assert", "1 + 1 == 2"));

        let diagnostic = pipeline.diagnose();

        assert!(diagnostic.has_assertions());
        assert!(diagnostic.has_assumptions());
        assert_eq!(diagnostic.num_obligations(), 2);

        // Diagnostic should be displayable
        let diag_str = format!("{}", diagnostic);
        assert!(diag_str.contains("obligations"));

        // Verify the pipeline also produces correct results
        let result = pipeline.verify();
        assert_eq!(result, VerifyResult::Verified);
    })
}

/// Test that proof functions properly isolate their contexts.
///
/// Each #[proof] function saves and restores the outer context,
/// so calling multiple proofs sequentially should not interfere.
#[test]
fn test_context_isolation() {
    common::with_clean_verification(|| {
        // First proof
        #[trust_vc::proof]
        fn isolated_proof_1() {
            trust_vc::assert!(1 == 1);
        }

        // Second proof with different assertions
        #[trust_vc::proof]
        fn isolated_proof_2() {
            trust_vc::assert!(2 == 2);
            trust_vc::assert!(3 == 3);
        }

        // Both should succeed independently — neither pollutes the other
        isolated_proof_1();
        isolated_proof_2();

        // After both proofs, the outer context should be clean
        // (each proof restored it)
        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(
            pipeline.context().obligations().len(),
            0,
            "Outer context should be empty after proof functions restore it"
        );
    })
}

/// Integration test showing the bridge solves issue #821
///
/// Issue #821: Proc macros generate markers but nothing reads them.
/// The bridge reads them INSIDE the proof function via auto-verify.
/// A successful proof call proves the bridge works end-to-end.
#[test]
fn test_bridge_solves_issue_821() {
    common::with_clean_verification(|| {
        // Issue #821: Proc macros generate markers but nothing reads them
        // The bridge reads markers via VerificationPipeline::collect_from_macros()
        // which is called inside the #[proof] expansion

        // Define and run a proof - the bridge verifies it internally
        #[trust_vc::proof]
        fn issue_821_proof() {
            trust_vc::assert!(42 == 42);
        }

        // Success = the bridge connected: macro -> VC -> ay -> Verified
        issue_821_proof();

        // Also verify the explicit registration path works
        trust_vc_core::verification_bridge::register_proof(
            "explicit_821",
            vec![ProofObligation::assert("explicit_check", "100 > 0")],
        );
        let pipeline = VerificationPipeline::collect_from_macros();
        assert!(
            !pipeline.context().obligations().is_empty(),
            "Explicit registration path also works"
        );
        let result = pipeline.verify();
        assert_eq!(result, VerifyResult::Verified);
    })
}
