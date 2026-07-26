// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test demonstrating actual integration between #[proof] functions and ay verification.
//!
//! This test addresses issue #791 - the missing integration between proof functions
//! and verification. It shows that proof functions DO verify their assertions via ay.

use trust_vc_core::verify_macro;

/// Test that proof functions actually use ay for verification
mod common;

#[test]
fn test_proof_function_uses_ay() {
    common::with_clean_verification(|| {
        // This proof function verifies its assertions via ay
        #[trust_vc::proof]
        fn valid_proof() {
            // This assertion is mathematically valid
            trust_vc::assert!(5 + 3 == 8);
        }

        // Execute the proof - it verifies internally via ay
        valid_proof();

        // If we get here, ay successfully verified the assertion
    })
}

/// Test that proof functions fail when ay finds a violation
#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_function_fails_on_invalid() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn invalid_proof() {
            // This assertion is mathematically false
            trust_vc::assert!(5 + 3 == 10);
        }

        // This should panic because ay will find the assertion is false
        invalid_proof();
    })
}

/// Test that proof functions handle assumptions correctly via ay
#[test]
fn test_proof_with_assumptions() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn proof_with_assumption() {
            // Use concrete values that don't require variable declaration
            trust_vc::assume!(10 > 5);
            trust_vc::assert!(10 > 0); // This follows from the assumption
        }

        // ay verifies that the assertion follows from the assumption
        proof_with_assumption();
    })
}

/// Test that contradictory assumptions are detected as vacuous truth (#2258).
///
/// With contradictory assumptions, the verifier returns Unknown (vacuous truth)
/// instead of silently verifying. The proof function panics accordingly.
#[test]
#[should_panic(expected = "Proof verification returned Unknown")]
fn test_contradictory_assumptions() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn contradictory() {
            // With contradictory assumptions, anything can be proven (vacuous truth)
            trust_vc::assume!(5 > 10); // False assumption
            trust_vc::assume!(5 < 3); // Another false assumption
                                      // Since assumptions are false, the implication is vacuously true
            trust_vc::assert!(5 == 5); // This passes even though assumptions contradict
        }

        // This actually succeeds due to vacuous truth
        contradictory();
    })
}

/// Test showing the integration flow
#[test]
fn test_integration_flow() {
    common::with_clean_verification(|| {
        // Step 1: Proof function collects obligations
        #[trust_vc::proof]
        fn demo_proof() {
            trust_vc::assume!(true);
            trust_vc::assert!(true);
        }

        // Step 2: Execute the proof function
        // This triggers:
        // - Collection of verification conditions
        // - Sending to ay encoder
        // - Getting verification result
        // - Acting on the result (pass or panic)
        demo_proof();

        // Step 3: Verify the context was used
        // After the proof function, context should be cleared
        // (since verification happened and succeeded)
        let ctx = verify_macro::get_context();
        assert!(
            ctx.is_none() || ctx.unwrap().obligations().is_empty(),
            "Context should be cleared after successful verification"
        );
    })
}

/// Demonstrates that proof functions work end-to-end
#[test]
fn test_end_to_end_proof_verification() {
    common::with_clean_verification(|| {
        // A realistic proof function
        #[trust_vc::proof]
        fn lemma_addition_commutative() {
            // Use concrete values to avoid variable declaration issues
            // Prove commutativity of addition
            trust_vc::assert!(7 + 3 == 3 + 7);

            // Prove identity (clippy warning suppressed for mathematical clarity)
            #[allow(clippy::identity_op)]
            {
                trust_vc::assert!(7 + 0 == 7);
                trust_vc::assert!(0 + 3 == 3);
            }
        }

        // Execute and verify via ay
        lemma_addition_commutative();

        println!("✓ Proof function successfully verified via ay");
    })
}

/// Test parameterized proof with BV overflow counterexample.
///
/// x > 0 && y > 0 does NOT imply x + y > 0 for i32: at x=i32::MAX, y=1 the
/// addition wraps around. ay correctly finds this counterexample.
#[test]
#[should_panic(expected = "Proof verification")]
fn test_param_proof_overflow_counterexample() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn overflow_proof(x: i32, y: i32) {
            trust_vc::assume!(x > 0);
            trust_vc::assume!(y > 0);
            trust_vc::assert!(x + y > 0);
        }

        // ay finds counterexample: x=i32::MAX, y=1 → overflow
        overflow_proof(5, 10);
    })
}

// ========================================================================
// PARAMETERIZED PROOF INTEGRATION TESTS (#1584)
// These exercise the proc-macro → variable registration → ay pipeline
// with actual function parameters (not just concrete literals).
// ========================================================================

/// Proof with one i32 parameter: x > 0 implies x >= 0.
/// Exercises: #[proof] param registration, assumes, assert, ay BV solving.
#[test]
fn test_param_proof_single_var() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn implication_proof(x: i32) {
            trust_vc::assume!(x > 0);
            trust_vc::assert!(x >= 0);
        }
        implication_proof(42);
    })
}

/// Proof with two parameters: bounded addition avoids overflow.
/// Exercises: multi-param registration, overflow-safe arithmetic.
#[test]
fn test_param_proof_bounded_addition() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn bounded_add(x: i32, y: i32) {
            trust_vc::assume!(x > 0);
            trust_vc::assume!(x < 1000);
            trust_vc::assume!(y > 0);
            trust_vc::assume!(y < 1000);
            trust_vc::assert!(x + y > 0);
        }
        bounded_add(5, 10);
    })
}

/// Proof with requires!/ensures! macros inside a #[proof] function.
/// Exercises: full contract macro expansion + variable type lookup + ay.
#[test]
fn test_param_proof_requires_ensures() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn contract_proof(n: i32) {
            trust_vc::requires!(n >= 0);
            trust_vc::requires!(n < 100);
            trust_vc::ensures!(n + 1 > 0);
        }
        contract_proof(50);
    })
}

/// Negative test: invalid postcondition with parameters caught by ay.
#[test]
#[should_panic(expected = "Proof verification")]
fn test_param_proof_invalid_ensures() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn bad_contract(x: i32) {
            trust_vc::assume!(x > 0);
            // x > 0 does NOT imply x > 100 — ay finds counterexample (e.g., x=1)
            trust_vc::assert!(x > 100);
        }
        bad_contract(1);
    })
}

/// Integration test showing the complete pipeline
#[test]
fn test_complete_verification_pipeline() {
    common::with_clean_verification(|| {
        // This test demonstrates the full integration:
        // 1. #[proof] macro expands the function
        // 2. trust_vc::assert! collects obligations
        // 3. verify_collected() is called automatically
        // 4. AYEncoder encodes the obligations
        // 5. ay solver checks satisfiability
        // 6. Result is returned and acted upon

        #[trust_vc::proof]
        fn pipeline_demo() {
            // Use concrete values to avoid variable declaration issues
            // Step 1: Add an assumption about a concrete value
            trust_vc::assume!(42 > 0);

            // Step 2: Assert something that follows
            trust_vc::assert!(42 >= 0);

            // All of this goes through ay for verification
        }

        // Execute the pipeline
        pipeline_demo();

        // Success means the full pipeline worked:
        // - Obligations collected
        // - Sent to ay
        // - Verified successfully
    })
}

#[test]
fn test_proof_call_postcondition_propagates_to_caller_2513() {
    let _ = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn caller_without_lemma_2513(x: i32) {
            trust_vc::assert!(x == 7);
        }

        caller_without_lemma_2513(5);
    });

    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn lemma_postcondition_2513(x: i32) {
            trust_vc::assume!(x == 7);
            trust_vc::ensures!(x == 7);
        }

        #[trust_vc::proof]
        fn caller_with_lemma_2513(x: i32) {
            lemma_postcondition_2513(x);
            trust_vc::assert!(x == 7);
        }

        caller_with_lemma_2513(5);
    });
}
