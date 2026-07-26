// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test that proof functions now auto-verify their obligations.
//! This tests the implementation of feature #203.
//!
//! Auto-verification is now implemented as of fixing issue #469.
//! Proof functions automatically verify their assertions and will
//! panic if verification fails.
//!
//! Test coverage includes:
//! - Basic proof functions with assumptions and assertions
//! - False assertions that should fail verification
//! - Contradictory assumptions
//! - Empty proof functions (no assertions or assumptions)
//! - Proof functions with parameters
//! - Proof functions with only assumptions (no assertions)

/// Test that proof functions automatically verify without manual verify_collected()
mod common;

#[test]
fn test_proof_auto_verifies() {
    common::with_clean_verification(|| {
        // This proof function should automatically verify its obligations
        #[trust_vc::proof]
        fn simple_proof() {
            trust_vc::assume!(5 > 3);
            trust_vc::assert!(5 > 3); // This should be verified automatically
        }

        // Call the proof function - it should verify internally
        simple_proof();

        // If we get here without panic, auto-verification worked
        // Test passes silently when successful
    })
}

/// Test that false assertions in proof functions should properly fail
/// Auto-verification is now implemented - this test should panic
#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_auto_verify_catches_false() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn false_proof() {
            trust_vc::assume!(5 > 3);
            trust_vc::assert!(3 > 5); // This is false and should fail once auto-verify is implemented
        }

        // This should panic with verification failure once feature #203 is implemented
        // Currently passes incorrectly because auto-verification isn't actually enabled
        false_proof();
    })
}

/// Test that contradictory assumptions are detected as vacuous truth (#2258).
///
/// Under contradictory assumptions (x > 5 AND x < 3), any assertion would be
/// vacuously true. Since #2258, the verifier detects this and returns Unknown
/// instead of Verified, causing the proof function to panic.
#[test]
#[should_panic(expected = "Proof verification returned Unknown")]
fn test_proof_contradictory_assumptions_vacuously_true() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn contradictory_proof() {
            let x = 4; // Define x
            trust_vc::assume!(x > 5);
            trust_vc::assume!(x < 3);
            // These assumptions are contradictory - ex falso, any assertion holds
            trust_vc::assert!(x == 4);
        }

        // Should NOT panic: contradictory assumptions make everything provable
        contradictory_proof();
    })
}

/// Test that empty proof functions (no obligations) produce an error.
///
/// An empty proof has no assertions or assumptions, so the verification
/// pipeline correctly errors with "empty context". This prevents
/// vacuous proofs from silently passing (soundness bug #808).
#[test]
#[should_panic(expected = "Proof verification error")]
fn test_empty_proof_function_errors() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn empty_proof() {
            // No assertions or assumptions - empty context is an error
        }

        // Should panic: empty context cannot be verified
        empty_proof();
    })
}

/// Test that parametric proofs detect overflow counterexamples.
///
/// For i32 bitvector arithmetic, x > 0 && y > 0 does NOT guarantee
/// x + y > 0 due to overflow (e.g., x=y=i32::MAX wraps negative).
/// The solver correctly finds this counterexample.
#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_with_parameters_overflow() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn proof_with_params(x: i32, y: i32) {
            trust_vc::assume!(x > 0);
            trust_vc::assume!(y > 0);
            trust_vc::assert!(x + y > 0); // Fails: overflow when x, y near i32::MAX
        }

        proof_with_params(5, 10);
    })
}

/// Test that proof functions with parameters catch invalid assertions
#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_with_params_fails() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn bad_proof_with_params(x: i32) {
            trust_vc::assume!(x > 0);
            trust_vc::assert!(x < 0); // Contradiction
        }

        bad_proof_with_params(5);
    })
}

/// Test that proof functions with only assumptions (no assertions) error (#808/#2258).
///
/// An assumptions-only context has nothing to prove, so the verifier returns
/// Error. The proof function panics accordingly.
#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_with_only_assumptions() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn assumptions_only() {
            let x = 5;
            trust_vc::assume!(x > 0);
            trust_vc::assume!(x < 10);
            // No assertions — nothing to prove → Error
        }

        assumptions_only();
    })
}

// Recursive proof functions are covered by fuel_encoding tests (encoder/fuel.rs)
// and the integration tests in test_recursive_verification.rs.
