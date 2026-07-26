// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Restored test coverage for verification scenarios deleted during
//! the Path B architectural pivot (commit 3a0dcad and follow-ups).
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline
//!
//! Part of #1597: Test count dropped 57% — these tests restore unique
//! coverage gaps identified through audit of deleted commits.
//!
//! Coverage areas restored:
//! 1. Multi-obligation collection (all assertions in one proof fn are checked)
//! 2. Proof parameter universal quantification (parameters become ay variables)
//! 3. Spec function assertion verification (positive + negative)
//! 4. External body contract verification (requires! through ay)
//! 5. Invalid termination detection (non-decreasing recursion)

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

// ============================================================================
// 1. Multi-obligation collection
// Verifies that multiple assertions in a single proof function are ALL checked,
// not just the first or last. Originally in test_proof_obligation_collection.rs.
// ============================================================================

#[test]
fn test_multi_obligation_all_true_verifies() {
    common::with_clean_verification(|| {
        // Declare universally quantified variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Collect multiple true obligations (commutativity + identity)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "commutative".to_string(),
            "x + y == y + x".to_string(),
            Some("multi_obligation_test".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "right_identity".to_string(),
            "x + 0 == x".to_string(),
            Some("multi_obligation_test".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "left_identity".to_string(),
            "0 + x == x".to_string(),
            Some("multi_obligation_test".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();

        // All three obligations should be collected
        assert!(
            pipeline.context().obligations().len() >= 3,
            "Expected at least 3 obligations, got {}",
            pipeline.context().obligations().len()
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "All true obligations should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multi_obligation_one_false_fails() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // First obligation: true
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "true_assertion".to_string(),
            "x + 0 == x".to_string(),
            Some("multi_obligation_test".to_string()),
        );
        // Second obligation: FALSE (x > x is never true)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_assertion".to_string(),
            "x > x".to_string(),
            Some("multi_obligation_test".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify because one assertion is false
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: false assertion 'x > x' was verified as correct!"
        );
    })
}

// ============================================================================
// 2. Proof parameter universal quantification
// Verifies that proof function parameters become universally quantified
// ay variables, not just concrete values. Originally in test_parameter_extraction.rs.
// ============================================================================

#[test]
fn test_parameter_universally_quantified_commutative() {
    common::with_clean_verification(|| {
        // Declare parameters as universally quantified
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());

        // Assert commutativity: this should verify for ALL a, b
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "param_commutes".to_string(),
            "a + b == b + a".to_string(),
            Some("parameter_universality_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Universal commutativity should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_parameter_universally_quantified_false_property() {
    common::with_clean_verification(|| {
        // Declare parameters as universally quantified
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());

        // Assert a * b == b + b: this is FALSE for most a, b
        // (only holds when a == 2)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_universal".to_string(),
            "a * b == b + b".to_string(),
            Some("parameter_universality_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "False universal property 'a * b == b + b' should not verify"
        );
    })
}

// ============================================================================
// 3. Spec function assertion verification
// Verifies that assertions inside #[spec] functions are collected and checked
// by ay. Originally in spec_verification_test.rs.
// ============================================================================

#[test]
fn test_spec_valid_property_verifies() {
    common::with_clean_verification(|| {
        // Simulate spec function assertion: n + 0 == n (identity)
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "spec_identity".to_string(),
            "n + 0 == n".to_string(),
            Some("spec_verification_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid spec assertion 'n + 0 == n' should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_spec_invalid_property_fails() {
    common::with_clean_verification(|| {
        // Simulate spec function with a false assertion: 5 == 6
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "spec_false".to_string(),
            "5 == 6".to_string(),
            Some("spec_verification_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: false spec assertion '5 == 6' was verified!"
        );
    })
}

// ============================================================================
// 4. External body contract verification
// Verifies that requires!() clauses on external_body functions are checked
// by ay. Originally in external_body_verification.rs.
// ============================================================================

#[test]
fn test_external_body_valid_precondition_verifies() {
    common::with_clean_verification(|| {
        // Simulate: external_body fn with requires!(x >= 0), called with x = 5
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x == 5 (the caller's concrete value)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );

        // The requires clause becomes an assertion at the call site
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "external_requires".to_string(),
            "x >= 0".to_string(),
            Some("external_body_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid external precondition (x=5, requires x>=0) should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_external_body_invalid_precondition_fails() {
    common::with_clean_verification(|| {
        // Simulate: external_body fn with requires!(x > 100), called with x = 5
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x == 5 (the caller's concrete value)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );

        // The requires clause should fail: 5 > 100 is false
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "external_requires".to_string(),
            "x > 100".to_string(),
            Some("external_body_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Invalid external precondition (x=5, requires x>100) should NOT verify"
        );
    })
}

// ============================================================================
// 5. Termination measure violations
// Verifies that the system rejects non-decreasing recursion patterns.
// Originally in termination_verification.rs.
// ============================================================================

#[test]
fn test_valid_termination_measure_verifies() {
    common::with_clean_verification(|| {
        // Simulate: #[decreases(n)] where recursive call uses n-1
        // Uses i32 with bounded range to avoid slow u64 bitvector solving
        verify_macro::collect_variable("n".to_string(), "i32".to_string());
        verify_macro::collect_variable("n_next".to_string(), "i32".to_string());

        // Assume 0 < n < 1000 (bounded to avoid overflow, non-base case)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_bounded".to_string(),
            "n > 0 && n < 1000".to_string(),
            None,
        );

        // Assume n_next == n - 1 (the recursive call uses n-1)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_next_def".to_string(),
            "n_next == n - 1".to_string(),
            None,
        );

        // Assert n_next < n (the decrease obligation)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "measure_decreases".to_string(),
            "n_next < n".to_string(),
            Some("termination_test".to_string()),
        );

        // Assert measure non-negative
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "measure_nonneg".to_string(),
            "n_next >= 0".to_string(),
            Some("termination_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid termination (n-1 < n when 0 < n < 1000) should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_termination_measure_fails() {
    common::with_clean_verification(|| {
        // Simulate: #[decreases(n)] where recursive call uses n (doesn't decrease!)
        // This is an infinite loop pattern: factorial(n) calls factorial(n)
        verify_macro::collect_variable("n".to_string(), "i32".to_string());
        verify_macro::collect_variable("n_next".to_string(), "i32".to_string());

        // Assume n > 0 (non-base case)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Bug: n_next == n (should be n - 1)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_next_def".to_string(),
            "n_next == n".to_string(),
            None,
        );

        // Assert n_next < n — this should FAIL because n == n is not < n
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "measure_decreases".to_string(),
            "n_next < n".to_string(),
            Some("termination_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: non-decreasing recursion (n_next == n) was verified!"
        );
    })
}

// ============================================================================
// 6. Combined requires + ensures verification
// Verifies that requires (assumptions) + ensures (assertions) work together.
// Originally in contracts_with_proof.rs.
// ============================================================================

#[test]
fn test_requires_enables_ensures_verification() {
    common::with_clean_verification(|| {
        // Simulate: fn add_five(x: i32) -> i32 { requires!(x > 0 && x < 1000); ensures!(result > x); x + 5 }
        // Uses bounded x to avoid overflow concerns with multiplication.
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Requires: x > 0 && x < 1000 (assumption, bounded to avoid overflow)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "requires_x_bounded".to_string(),
            "x > 0 && x < 1000".to_string(),
            None,
        );

        // Function body: result == x + 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "body_result".to_string(),
            "result == x + 5".to_string(),
            None,
        );

        // Ensures: result > x (assertion to verify)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ensures_result_gt_x".to_string(),
            "result > x".to_string(),
            Some("contract_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 && x < 1000 => x + 5 > x should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_insufficient_for_ensures() {
    common::with_clean_verification(|| {
        // Simulate: fn add_one(x: i32) -> i32 { requires!(x >= 0); ensures!(result > 10); x + 1 }
        // The ensures should FAIL: x + 1 > 10 is not guaranteed by x >= 0
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Requires: x >= 0
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "requires_x_nonneg".to_string(),
            "x >= 0".to_string(),
            None,
        );

        // Body: result == x + 1
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "body_result".to_string(),
            "result == x + 1".to_string(),
            None,
        );

        // Ensures: result > 10 — should FAIL (e.g., x=0 gives result=1)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ensures_result_gt_10".to_string(),
            "result > 10".to_string(),
            Some("contract_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Insufficient requires should not verify ensures: x >= 0 does not imply x + 1 > 10"
        );
    })
}

// ============================================================================
// 7. Via-fn proof verification
// Verifies that via_fn proof assertions go through ay verification.
// Originally in test_via_fn_verification.rs.
// ============================================================================

#[test]
fn test_via_fn_valid_proof_verifies() {
    common::with_clean_verification(|| {
        // Simulate: via_fn proof that n / 2 < n when n > 1
        // Uses i32 to avoid slow u64 bitvector solving
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Precondition
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_gt_1".to_string(),
            "n > 1".to_string(),
            None,
        );

        // The proof assertion
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "shift_decreases".to_string(),
            "n / 2 < n".to_string(),
            Some("via_fn_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "n > 1 => n/2 < n should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_via_fn_invalid_proof_fails() {
    common::with_clean_verification(|| {
        // Simulate: invalid via_fn proof that n + 1 < n
        // Uses i32 to avoid slow u64 bitvector solving
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_bounded".to_string(),
            "n >= 0 && n < 1000".to_string(),
            None,
        );

        // False assertion: n + 1 < n is never true for unsigned
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "invalid_via_fn".to_string(),
            "n + 1 < n".to_string(),
            Some("via_fn_test".to_string()),
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: 'n + 1 < n' was verified as correct!"
        );
    })
}

// ============================================================================
// 8. Proof function with auto-verify: multiple lemma calls
// Verifies that calling multiple proof functions in sequence works correctly.
// Originally in test_proof_verification.rs.
// ============================================================================

#[test]
fn test_proof_fn_basic_auto_verify() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn lemma_addition_identity() {
            trust_vc::assume!(5 > 0);
            trust_vc::assert!(5 + 0 == 5);
        }

        // Should not panic — auto-verify should pass
        lemma_addition_identity();
    })
}

#[test]
#[should_panic(expected = "Proof verification")]
fn test_proof_fn_auto_verify_catches_false() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn lemma_false_claim() {
            trust_vc::assert!(5 + 5 == 11);
        }

        // Should panic — auto-verify should catch the false assertion
        lemma_false_claim();
    })
}
