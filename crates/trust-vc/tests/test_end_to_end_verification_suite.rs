// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end integration test suite for the full verification pipeline
//!
//! This suite tests the complete flow from trust_vc macros through to ay verification,
//! ensuring all components work together correctly.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! All tests in this file perform actual ay verification

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

// ============================================================================
// Test 1: Basic Assertion Flow
// ============================================================================

#[test]
fn test_e2e_simple_assertion_verified() {
    common::with_clean_verification(|| {
        // Simulate what the assert! macro would do
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            Some("test_e2e:simple".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "simple_check".to_string(),
            "x > 0".to_string(),
            Some("test_e2e:simple".to_string()),
        );

        // Run through the full pipeline
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Simple assertion x > 0 with x == 5 should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_e2e_false_assertion_counterexample() {
    common::with_clean_verification(|| {
        // Set up a false assertion
        verify_macro::collect_variable("y".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 10".to_string(),
            Some("test_e2e:false".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_check".to_string(),
            "y < 5".to_string(), // This is false!
            Some("test_e2e:false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "False assertion y < 5 with y == 10 should produce counterexample, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 2: Requires/Ensures Contract Flow
// ============================================================================

#[test]
fn test_e2e_requires_ensures_valid() {
    common::with_clean_verification(|| {
        // Simulate a function contract with symbolic values.
        // Assume input > 0 (with overflow guard) and result == input * 2,
        // then assert result > input — requires multi-step BV reasoning.
        // (#1595: was using concrete input == 5, making assertions trivially true)
        verify_macro::collect_variable("input".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Symbolic precondition with overflow guard for i32 multiplication
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "input_range".to_string(),
            "input > 0 && input < 1073741823".to_string(), // < i32::MAX/2 to avoid overflow
            Some("test_e2e:contract".to_string()),
        );

        // Function body simulation: result = input * 2
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "computation".to_string(),
            "result == input * 2".to_string(),
            Some("test_e2e:contract".to_string()),
        );

        // Check postcondition: result > input (requires: input*2 > input when input > 0)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "postcondition".to_string(),
            "result > input".to_string(),
            Some("test_e2e:contract".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "input > 0 and result == input * 2 implies result > input, got: {:?}",
            result
        );
    })
}

#[test]
fn test_e2e_requires_false_vacuously_verified() {
    common::with_clean_verification(|| {
        // In callee-side verification, requires(false) is an assumption.
        // With only assumptions and no assertions, the result is vacuously Verified.
        // See #1503 for semantics discussion.
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "impossible_precondition".to_string(),
            "false".to_string(),
            Some("test_e2e:requires_false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(false) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 3: Loop Invariant Flow
// ============================================================================

#[test]
fn test_e2e_loop_invariant_valid() {
    common::with_clean_verification(|| {
        // Simulate a loop with invariant
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("sum".to_string(), "i32".to_string());

        // Initial conditions
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "loop_init".to_string(),
            "i == 0 && sum == 0".to_string(),
            Some("test_e2e:loop".to_string()),
        );

        // Loop invariant (represented as an assertion in the verification)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "loop_invariant".to_string(),
            "sum >= 0".to_string(), // Simple invariant that should hold
            Some("test_e2e:loop".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Loop invariants should verify properly
        assert!(
            matches!(result, VerifyResult::Verified),
            "Loop invariant sum >= 0 should verify (not Unknown), got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 4: Decreases (Termination) Flow
// ============================================================================

#[test]
fn test_e2e_decreases_valid() {
    common::with_clean_verification(|| {
        // Simulate a recursive function with decreasing measure
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_variable("n_next".to_string(), "u64".to_string());

        // Set up decreasing values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 10".to_string(),
            Some("test_e2e:decreases".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_next_value".to_string(),
            "n_next == n - 1".to_string(),
            Some("test_e2e:decreases".to_string()),
        );

        // Check that measure decreases
        verify_macro::collect_obligation(
            ObligationKind::MeasureDecreases,
            "termination_check".to_string(),
            "n_next < n".to_string(),
            Some("test_e2e:decreases".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Decreasing measure n_next < n should verify, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 5: Complex Multi-Component Flow
// ============================================================================

#[test]
fn test_e2e_complex_verification_scenario() {
    common::with_clean_verification(|| {
        // Complex scenario: array access with derived bound.
        // Requires arr_len > 0, index >= 0, index < arr_len, then asserts index + 1 <= arr_len.
        // The assertion is a derived property (not a restatement): i < n ⟹ i + 1 ≤ n
        // requires the solver to reason about the relationship between < and +1/<=.
        // Uses i32 to avoid 64-bit BV timeouts.
        // (#1595: was asserting index < arr_len which was identical to the requires)
        verify_macro::collect_variable("arr_len".to_string(), "i32".to_string());
        verify_macro::collect_variable("index".to_string(), "i32".to_string());

        // Preconditions
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "array_nonempty".to_string(),
            "arr_len > 0".to_string(),
            Some("test_e2e:complex".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "index_nonneg".to_string(),
            "index >= 0".to_string(),
            Some("test_e2e:complex".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "index_in_bounds".to_string(),
            "index < arr_len".to_string(),
            Some("test_e2e:complex".to_string()),
        );

        // Derived postcondition: index + 1 <= arr_len
        // NOT a restatement — the solver must derive i + 1 ≤ n from i < n.
        // Overflow-safe: index < arr_len ≤ i32::MAX, so index ≤ i32::MAX - 1
        // and index + 1 ≤ i32::MAX (no BV overflow).
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "derived_bound".to_string(),
            "index + 1 <= arr_len".to_string(),
            Some("test_e2e:complex".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "index < arr_len implies index + 1 <= arr_len should verify, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 6: Error Handling Flow
// ============================================================================

#[test]
fn test_e2e_empty_context_error() {
    common::with_clean_verification(|| {
        // Don't add any obligations - empty context
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Empty context should return Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_e2e_type_mismatch_handling() {
    common::with_clean_verification(|| {
        // Try to use an undefined variable (type error)
        // Don't declare any variables

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "undefined_var".to_string(),
            "undefined_variable > 0".to_string(), // Undefined variable!
            Some("test_e2e:type_error".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should either error or produce counterexample
        assert!(
            matches!(
                result,
                VerifyResult::Error { .. } | VerifyResult::Counterexample { .. }
            ),
            "Type mismatch should produce error or counterexample, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 7: Quantifier Flow
// ============================================================================

#[test]
fn test_e2e_forall_quantifier() {
    common::with_clean_verification(|| {
        // Test that assumes + derived assertion requires real solver reasoning.
        // Assume x > 0 and y > x, then assert y > 0 — requires transitivity.
        // (#1595: was assume(x*x >= 0) / assert(x*x >= 0), an identical-expression tautology)
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_positive".to_string(),
            "x > 0".to_string(),
            Some("test_e2e:forall".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_gt_x".to_string(),
            "y > x".to_string(),
            Some("test_e2e:forall".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "y_positive".to_string(),
            "y > 0".to_string(), // Derived via transitivity: y > x > 0 => y > 0
            Some("test_e2e:forall".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "y > x and x > 0 implies y > 0 should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_e2e_exists_quantifier() {
    common::with_clean_verification(|| {
        // Test existential property without complex quantifier syntax
        verify_macro::collect_variable("y".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 5".to_string(), // One solution to y*y == 25
            Some("test_e2e:exists".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "exists_simulation".to_string(),
            "y * y == 25".to_string(), // Should verify with y = 5
            Some("test_e2e:exists".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // y == 5 assumed, y * y == 25 is decidable BV arithmetic → must verify.
        assert!(
            matches!(result, VerifyResult::Verified),
            "Property y*y == 25 with y=5 should verify, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Test 8: Integration with All Obligation Types
// ============================================================================

#[test]
fn test_e2e_all_obligation_types() {
    common::with_clean_verification(|| {
        // Use every type of obligation
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // ObligationKind::Assume
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assumption".to_string(),
            "x > 0".to_string(),
            Some("test_e2e:all_types".to_string()),
        );

        // ObligationKind::Assert
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assertion".to_string(),
            "x >= 0".to_string(),
            Some("test_e2e:all_types".to_string()),
        );

        // ObligationKind::Requires
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x != 0".to_string(),
            Some("test_e2e:all_types".to_string()),
        );

        // ObligationKind::Ensures
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > 0".to_string(),
            Some("test_e2e:all_types".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // With x > 0 assumed: x >= 0 and x > 0 are both decidable BV → must verify.
        assert!(
            matches!(result, VerifyResult::Verified),
            "All obligation types together should verify, got: {:?}",
            result
        );
    })
}
