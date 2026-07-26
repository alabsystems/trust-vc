// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Runtime panic tests for #[proof] functions
//!
//! These tests ensure that invalid proof functions cause runtime panics.
//! Each test uses #[should_panic] to verify that Rust runtime assertions fire.
//!
//! VERIFICATION LEVEL: RUNTIME
//! Tests in this file check runtime panic behavior, NOT ay SMT verification.
//! The #[proof] macro triggers assert_by! panics at runtime — no ay invocation.

use trust_vc::{assert_by, proof};
mod common;

fn sum(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}

#[cfg(test)]
mod negative_proof_tests {
    use super::*;

    /// Test that proof functions with false assertions are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_false_proof_assertion_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with a false assertion
            #[proof]
            fn invalid_proof() {
                assert_by!(1 == 2); // Obviously false
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            invalid_proof();
        })
    }

    /// Test that proof functions claiming invalid lemmas are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_invalid_lemma_must_fail() {
        common::with_clean_verification(|| {
            // Define a lemma that claims something false
            #[proof]
            fn lemma_all_positive(x: i32) {
                // This claims all integers are positive (false for negatives)
                assert_by!(x > 0); // False when x <= 0
            }

            // Invoke the lemma with a negative number to trigger verification
            // This SHOULD panic with "Proof verification failed"
            lemma_all_positive(-5); // -5 is not > 0
        })
    }

    /// Test that proof functions with contradictory assertions are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_contradictory_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with contradictory assertions
            #[proof]
            fn contradictory_proof() {
                let x = 5;
                assert_by!(x > 10); // x = 5, so this is false
                assert_by!(x < 3); // Also false
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            contradictory_proof();
        })
    }

    /// Test that recursive proof functions with invalid base cases are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_invalid_recursive_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a recursive proof function with an invalid base case
            #[proof]
            fn lemma_sum_wrong(n: u32) {
                if n == 0 {
                    assert_by!(sum(0) == 1); // Wrong: sum(0) should be 0
                } else {
                    lemma_sum_wrong(n - 1);
                    assert_by!(sum(n) == sum(n - 1) + n);
                }
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            lemma_sum_wrong(3);
        })
    }

    /// Test that proof functions with division by zero are rejected
    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn test_proof_division_by_zero_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with division by zero
            #[proof]
            #[allow(unconditional_panic)] // Intentional - testing division by zero rejection
            fn invalid_division_proof() {
                let x = 0;
                assert_by!(1 / x == 1); // Division by zero
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            invalid_division_proof();
        })
    }

    /// Test that proof functions claiming false invariants are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_false_invariant_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with a false invariant claim
            #[proof]
            fn lemma_false_invariant() {
                // Claim that for all x, x^2 < x (false for x > 1)
                let x = 2;
                assert_by!(x * x < x); // 4 < 2 is false
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            lemma_false_invariant();
        })
    }

    /// Test that proof functions with incorrect arithmetic are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_incorrect_arithmetic_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with incorrect arithmetic claims
            #[proof]
            fn lemma_bad_math() {
                // Incorrect arithmetic claims
                assert_by!(2 + 3 == 6); // Should be 5
                assert_by!(10 - 4 == 5); // Should be 6
                assert_by!(3 * 3 == 10); // Should be 9
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            lemma_bad_math();
        })
    }

    /// Test that proof functions with impossible postconditions are rejected
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_impossible_postcondition_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with impossible postconditions
            #[proof]
            fn lemma_impossible_ensures() -> i32 {
                let result = 5;
                // Claim the result is both > 10 and < 3 (impossible)
                trust_vc::ensures!(result > 10);
                trust_vc::ensures!(result < 3);
                result
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            let _ = lemma_impossible_ensures();
        })
    }

    /// Test that proof functions with overflow are handled correctly
    #[test]
    #[should_panic(expected = "attempt to add with overflow")]
    fn test_overflow_in_proof_must_fail() {
        common::with_clean_verification(|| {
            // Define a proof function with overflow
            #[proof]
            #[allow(arithmetic_overflow)] // Intentional - testing overflow rejection
            fn lemma_overflow() {
                let max_u32: u32 = 4294967295; // u32::MAX
                assert_by!(max_u32 + 1 > max_u32); // Overflow in u32
            }

            // Invoke the proof function to trigger verification
            // This SHOULD panic with "Proof verification failed"
            lemma_overflow();
        })
    }
}
