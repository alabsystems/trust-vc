// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comprehensive tests for #[proof] functions
//!
//! Tests that proof functions:
//! 1. Collect verification conditions correctly
//! 2. Document the current recursive-proof limitation
//! 3. Fail closed on unsupported verification syntax
//! 4. Work with assertions and assumptions

use trust_vc::{assert_by, assume, forall, proof};

/// Documentation test showing proof function usage
/// ```
/// use trust_vc::proof;
///
/// #[proof]
/// fn lemma_positive_sum(a: u32, b: u32) {
///     trust_vc::assert_by!(a + b >= a);
///     trust_vc::assert_by!(a + b >= b);
/// }
///
/// // Proof functions can be called like normal functions
/// lemma_positive_sum(10, 20);
/// ```
pub fn proof_function_example() {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test 1: Basic proof function that should verify
    #[test]
    fn test_proof_function_basic_valid() {
        #[proof]
        fn lemma_addition_commutative(a: u32, b: u32) {
            // This should verify - addition is commutative
            assert_by!(a + b == b + a);
        }

        // Call the proof function - it should not panic
        lemma_addition_commutative(5, 10);
    }

    /// Test 2: Proof function with invalid assertion should fail verification.
    /// The auto-verify mechanism in #[proof] detects the false assertion and panics.
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_proof_function_invalid_assertion() {
        #[proof]
        fn lemma_false_claim() {
            assert_by!(5 < 3);
        }

        lemma_false_claim();
    }

    /// Test 3: Recursive proof function for induction.
    /// Recursive proof verification is still incomplete: trust_vc lacks the
    /// fuel/reveal machinery needed to make recursive proof calls usable as
    /// induction steps, so this remains a known failure.
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_proof_function_recursive() {
        #[proof]
        fn lemma_sum_nonnegative(n: u32) {
            if n == 0 {
                assert_by!(n == 0);
            } else {
                assume!(n > 0);
                lemma_sum_nonnegative(n - 1);
            }
        }

        lemma_sum_nonnegative(10);
    }

    /// Test 4: Proof function with assumptions
    #[test]
    fn test_proof_function_with_assumptions() {
        #[proof]
        fn lemma_bounded_increment(x: i32) {
            assume!(x > 0);
            assume!(x < 100);
            // If x is between 1 and 99, then x + 1 > 1
            assert_by!(x + 1 > 1);
        }

        lemma_bounded_increment(10);
    }

    /// Test 5: Proof function with a top-level mutable-reference update.
    /// The MVP supports `&mut` parameters by rewriting `*x` reads/stores into
    /// SSA-style shadow values inside the proof body while keeping the runtime
    /// store in place.
    #[test]
    fn test_proof_function_mut_ref_update() {
        #[proof]
        fn lemma_mut_ref_update(x: &mut i32) {
            assume!(*x >= 0);
            assume!(*x < 1000);
            *x = *x + 1;
            let current: i32 = *x;
            trust_vc::assert!(current > 0);
            trust_vc::ensures!(*x == old!(*x) + 1);
        }

        let mut counter = 10;
        lemma_mut_ref_update(&mut counter);
        assert_eq!(
            counter, 11,
            "proof body should keep the direct runtime store"
        );
    }

    /// Test 6: Proof function with forall quantifier
    /// Note: ay-dpll returns Unknown for universal BV quantifiers, so this test
    /// verifies macro compilation only (not pipeline verification). See #749.
    #[test]
    fn test_proof_function_with_forall() {
        // Verify forall! compiles inside a proof-like context
        // Cannot use #[proof] because pipeline verification panics on Unknown
        // when ay-dpll can't verify universal BV quantifiers
        #[allow(clippy::eq_op)]
        let _ = forall!(|x: i32| x == x);
    }

    /// Test 7: Proof function calling other proof functions.
    /// Uses i32 with explicit bounds to avoid BV32 overflow in `a + b >= a`.
    /// (u32 is encoded as signed BV32 — large unsigned values appear negative.)
    #[test]
    fn test_proof_function_composition() {
        #[proof]
        fn lemma_helper(x: i32) {
            assume!(x >= 0);
            assume!(x < 1000);
            assert_by!(x + 1 > x);
        }

        #[proof]
        fn lemma_main(a: i32, b: i32) {
            assume!(a >= 0);
            assume!(a < 1000);
            assume!(b >= 0);
            assume!(b < 1000);
            lemma_helper(a);
            lemma_helper(b);
            assert_by!(a + b >= a);
        }

        lemma_main(5, 10);
    }

    /// Test 8: Complex proof with multiple conditions.
    /// Bounds a,b,c < 10000 prevent BV32 overflow in (a+b+c)/2 computations.
    /// Gated: BV solver timeout >10s. Needs v2 incremental solving. (#2658 Category H)
    #[test]
    #[cfg(feature = "expensive-tests")]
    fn test_proof_function_complex() {
        #[proof]
        fn lemma_triangle_inequality(a: i32, b: i32, c: i32) {
            assume!(a > 0);
            assume!(b > 0);
            assume!(c > 0);
            assume!(a < 10000);
            assume!(b < 10000);
            assume!(c < 10000);
            assume!(a + b > c);
            assume!(b + c > a);
            assume!(a + c > b);

            assert_by!(a + b + c > 0);
            assert_by!((a + b + c) / 2 > 0);
        }

        lemma_triangle_inequality(3, 4, 5);
    }

    /// Test 9: Proof function with generic types verifies via Poly encoding.
    /// Generic type parameters are Box'd to the Poly sort, enabling
    /// ay-dpll to verify identity-like lemmas over generics.
    #[test]
    fn test_proof_function_generic() {
        #[proof]
        fn lemma_identity<T: PartialEq + Copy>(x: T) -> T {
            let result = x;
            assert_by!(result == x);
            result
        }

        let _ = lemma_identity(42);
    }

    /// Test 10: Proof function that should fail with wrong assumptions
    /// NOTE: Like test 2, this doesn't actually test verification because
    /// proof functions don't execute at runtime. Needs actual verifier invocation.
    #[test]
    #[should_panic]
    fn test_proof_function_contradictory() {
        #[proof]
        fn lemma_contradiction() {
            assume!(5 > 10);
            assume!(10 > 5);
            // Contradictory assumptions should make this fail
            assert_by!(5 == 10);
        }

        lemma_contradiction();
    }
}
