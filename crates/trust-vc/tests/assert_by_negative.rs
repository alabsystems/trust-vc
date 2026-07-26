// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for assert_by! macro - verify that invalid assertions fail
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid assertions
//!
//! These tests verify that the assert_by! macro properly rejects invalid proofs
//! and generates appropriate counterexamples.

use trust_vc::assert_by;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

mod common;

#[test]
fn test_assert_by_false_condition_fails() {
    common::with_clean_verification(|| {
        // Test with concrete values that ay can evaluate
        // This should fail - asserting something that is false
        assert_by!(5 == 10); // 5 is not equal to 10

        // Verify it produces a counterexample
        let (_obligation_name, _model) =
            expect_counterexample().expect("False assertion should produce counterexample");
    })
}

#[test]
fn test_assert_by_contradiction_fails() {
    common::with_clean_verification(|| {
        // Test with concrete values - these are contradictory assertions
        assert_by!(5 > 10); // 5 > 10 is false
        assert_by!(10 < 5); // 10 < 5 is also false

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Contradictory assertions should produce counterexample");
    })
}

#[test]
fn test_assert_by_invalid_arithmetic_fails() {
    common::with_clean_verification(|| {
        // Invalid arithmetic property with concrete values
        // 7 * 7 = 49, but 7 + 7 = 14, so this is false
        assert_by!(7 * 7 == 7 + 7); // 49 == 14 is false

        let (_obligation_name, _model) =
            expect_counterexample().expect("Invalid arithmetic should produce counterexample");
    })
}

#[test]
fn test_assert_by_proof_with_wrong_proof_fails() {
    common::with_clean_verification(|| {
        // Test with concrete negative value
        // -5 > 0 is false
        assert_by!(-5 > 0); // Should fail since -5 is not greater than 0

        let (_obligation_name, _model) =
            expect_counterexample().expect("Wrong proof should produce counterexample");
    })
}

#[test]
fn test_assert_by_unsatisfiable_constraint_fails() {
    common::with_clean_verification(|| {
        // Unsatisfiable constraint with concrete values
        // A value x can't satisfy x > 15 AND x < 5 at the same time
        // We'll test that 10 fails this impossible constraint
        // Use two separate assertions to avoid clippy simplification
        assert_by!(10 > 15); // First part of impossible constraint
        assert_by!(10 < 5); // Second part of impossible constraint

        // Use the verification pipeline directly to see what's happening
        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();

        // Check that it's not Verified (since the constraint is unsatisfiable)
        assert!(
            !matches!(verify_result, VerifyResult::Verified),
            "Unsatisfiable constraints should not verify - got: {:?}",
            verify_result
        );
    })
}

#[test]
fn test_assert_by_division_by_zero_fails() {
    common::with_clean_verification(|| {
        // Division by zero should be caught
        // Note: We're testing verification, not runtime behavior
        // The actual division won't execute - just the verification condition
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "div_by_zero".to_string(),
            "10 / 0 == 5".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // This might return Error or Counterexample depending on ay's handling
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Division by zero should not verify"
        );
    })
}

#[test]
fn test_assert_by_let_binding_false_condition_fails() {
    common::with_clean_verification(|| {
        // Fix #845: let bindings are now inlined into the condition.
        // A false condition after substitution should still produce a counterexample.
        // `let x = 5; x == 10` becomes `(5) == 10` which is false.
        assert_by! {
            let x = 5;
            x == 10
        };

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "False condition with let binding should not verify - got: {:?}",
            result
        );
    })
}
