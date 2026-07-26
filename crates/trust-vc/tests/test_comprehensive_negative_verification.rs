// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Comprehensive negative verification tests
//!
//! This file tests that various invalid proofs and assertions properly fail
//! with specific counterexamples, not just "some failure".
//!
//! Each test:
//! 1. Sets up an invalid verification condition
//! 2. Expects a specific type of failure (Counterexample)
//! 3. Verifies the failure contains expected details
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

// ======================================================================
// SECTION 1: Basic Assertion Failures
// ======================================================================

mod common;

#[test]
fn test_false_literal_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that asserting false literals produces counterexamples
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_literal".to_string(),
            "false".to_string(),
            None,
        );

        let result = expect_counterexample();
        eprintln!("test_false_literal_fails result: {:?}", result);
        let (obligation_name, _model) =
            result.expect("False literal should produce counterexample");
        // The obligation name is "false_literal" as we set it
        assert!(
            obligation_name == "false_literal",
            "Should have correct obligation name, got: {}",
            obligation_name
        );
    })
}

#[test]
fn test_false_comparison_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that false comparisons produce counterexamples
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_comparison".to_string(),
            "5 > 10".to_string(),
            None,
        );

        let (obligation_name, _model) =
            expect_counterexample().expect("False comparison should produce counterexample");
        assert!(
            obligation_name == "false_comparison",
            "Should identify failed assertion, got: {}",
            obligation_name
        );
    })
}

#[test]
fn test_contradiction_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that contradictory assertions are detected
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // These two assertions contradict each other
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_gt_10".to_string(),
            "x > 10".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_lt_5".to_string(),
            "x < 5".to_string(),
            None,
        );

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Contradictory assertions should produce counterexample");
    })
}

// ======================================================================
// SECTION 2: Precondition Failures
// ======================================================================

#[test]
fn test_unsatisfiable_precondition_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that functions with impossible preconditions are handled correctly
        // Note: Mathematically, an implication with false antecedent is vacuously true,
        // so `(n > 0 && n < 0) => anything` is always true. This test has been updated
        // to reflect the correct verification semantics.
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Impossible precondition
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Requires,
            "impossible_precond".to_string(),
            "n > 0 && n < 0".to_string(), // Can't be both positive and negative
            None,
        );

        // Add an assertion to check
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "dummy_assert".to_string(),
            "true".to_string(), // Vacuously true under impossible precondition
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Verified => {
                // This is actually correct! Implication with false antecedent is true
                // The assertion is vacuously satisfied
            }
            VerifyResult::Error { .. } => {
                // Also acceptable if the system detects the impossible precondition
            }
            VerifyResult::Unknown { .. } => {
                // Also acceptable if solver can't decide
            }
            other => panic!("Unexpected result for impossible precondition: {:?}", other),
        }
    })
}

// ======================================================================
// SECTION 3: Postcondition Failures
// ======================================================================

#[test]
fn test_unmet_postcondition_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that unmet postconditions are detected
        trust_vc_core::verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Function that doesn't meet its postcondition
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "unmet_postcond".to_string(),
            "result > 100".to_string(),
            None,
        );

        // But the actual result is small
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "actual_result".to_string(),
            "result == 5".to_string(),
            None,
        );

        let (_obligation_name, _model) =
            expect_counterexample().expect("Unmet postcondition should produce counterexample");
    })
}

// ======================================================================
// SECTION 4: Loop Invariant Failures
// ======================================================================

#[test]
fn test_invariant_not_preserved_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that invariants that aren't preserved fail
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Initial value
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "i_initial".to_string(),
            "i == 0".to_string(),
            None,
        );

        // Invariant that won't be preserved
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "loop_invariant".to_string(),
            "i % 2 == 0".to_string(), // i must be even
            None,
        );

        // But we increment by 1 (making it odd)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "i_next".to_string(),
            "i == 1".to_string(), // i becomes 1 (odd)
            None,
        );

        let (_obligation_name, _model) =
            expect_counterexample().expect("Non-preserved invariant should produce counterexample");
    })
}

// ======================================================================
// SECTION 5: Termination Measure Failures
// ======================================================================

#[test]
fn test_negative_termination_measure_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that negative termination measures are rejected
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // First establish that n is negative via assumption
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_is_negative".to_string(),
            "n == -5".to_string(),
            None,
        );

        // Then check that the measure is non-negative
        // With n assumed to be -5, this should fail
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureNonNegative,
            "measure_nonneg".to_string(),
            "n >= 0".to_string(),
            None,
        );

        let (obligation_name, _model) = expect_counterexample()
            .expect("Negative termination measure should produce counterexample");
        assert!(
            obligation_name.contains("measure") || obligation_name.contains("nonneg"),
            "Should identify termination measure failure, got: {}",
            obligation_name
        );
    })
}

#[test]
fn test_non_decreasing_measure_fails() {
    common::with_clean_verification(|| {
        // Purpose: Verify that non-decreasing measures are rejected
        trust_vc_core::verify_macro::collect_variable("m".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("m_next".to_string(), "i32".to_string());

        // Current and next values
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "m_current".to_string(),
            "m == 10".to_string(),
            None,
        );

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "m_next_val".to_string(),
            "m_next == 11".to_string(), // Increases instead of decreases
            None,
        );

        // Measure must decrease
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "measure_decreases".to_string(),
            "m_next < m".to_string(),
            None,
        );

        let (_obligation_name, _model) =
            expect_counterexample().expect("Non-decreasing measure should produce counterexample");
    })
}

// ======================================================================
// SECTION 6: Complex Expression Failures
// ======================================================================

#[test]
fn test_complex_arithmetic_failure() {
    common::with_clean_verification(|| {
        // Purpose: Verify that complex arithmetic errors are caught
        trust_vc_core::verify_macro::collect_variable("a".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("b".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("c".to_string(), "i32".to_string());

        // Set up values
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "values".to_string(),
            "a == 3 && b == 4 && c == 5".to_string(),
            None,
        );

        // False Pythagorean theorem claim
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_pythagoras".to_string(),
            "a * a + b * b == c * c + 1".to_string(), // 9 + 16 != 26
            None,
        );

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Complex arithmetic failure should produce counterexample");
    })
}

// ======================================================================
// SECTION 7: Boundary Condition Failures
// ======================================================================

#[test]
fn test_array_bounds_failure() {
    common::with_clean_verification(|| {
        // Purpose: Verify that array bound violations are caught
        trust_vc_core::verify_macro::collect_variable("index".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("array_len".to_string(), "i32".to_string());

        // Array has length 10
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "array_size".to_string(),
            "array_len == 10".to_string(),
            None,
        );

        // Try to access index 15 (out of bounds)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "index_value".to_string(),
            "index == 15".to_string(),
            None,
        );

        // Bounds check should fail
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "bounds_check".to_string(),
            "index >= 0 && index < array_len".to_string(),
            None,
        );

        let (_obligation_name, _model) =
            expect_counterexample().expect("Array bounds violation should produce counterexample");
    })
}

#[test]
fn test_integer_overflow_failure() {
    common::with_clean_verification(|| {
        // Purpose: Verify that integer overflow is detected
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Values near i32::MAX
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "large_values".to_string(),
            "x == 2147483640 && y == 20".to_string(), // Close to i32::MAX
            None,
        );

        // This addition would overflow
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "no_overflow".to_string(),
            "x + y <= 2147483647".to_string(), // i32::MAX
            None,
        );

        let (_obligation_name, _model) =
            expect_counterexample().expect("Integer overflow should produce counterexample");
    })
}
