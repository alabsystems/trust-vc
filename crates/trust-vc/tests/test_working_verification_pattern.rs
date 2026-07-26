// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test that demonstrates using the WORKING verification pattern from test_actual_verification.rs
//!
//! This pattern directly uses VerificationContext which:
//! - Actually calls ay for verification (no mocking)
//! - Provides clear APIs: declare_var, add_assume, add_assert, verify
//! - Returns real verification results (Verified, Counterexample, Unknown)
//!
//! This pattern should replace the fake pipeline and verify_macro approaches
//! that don't actually perform verification.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

#[test]
fn test_loop_invariant_with_working_pattern() {
    // Build a verification context using the WORKING pattern
    let mut ctx = VerificationContext::new();

    // Declare loop variable
    ctx.declare_var_parsed("i", "i32");

    // Model inductive case: assume invariant holds at loop entry
    // and that we're in the loop (i < 10)
    ctx.push_assume("invariant_holds", "i >= 0");
    ctx.push_assume("loop_guard", "i < 10");

    // After loop body (i increments), invariant should still hold
    // This models: i' = i + 1, and we need to prove i' >= 0
    ctx.push_assert("invariant_preserved", "(i + 1) >= 0");

    // Actually verify with ay!
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Loop invariant i >= 0 should verify when starting from i == 0, got: {:?}",
        result
    );
}

#[test]
fn test_invalid_invariant_properly_fails() {
    // Test that an invalid invariant is correctly rejected
    let mut ctx = VerificationContext::new();

    // Declare loop variable
    ctx.declare_var_parsed("i", "i32");

    // Initial value: i starts at 0
    // Then after some iterations, i could be any positive value
    // We want to check if "i == 0" holds as an invariant

    // Model that i could be any value >= 0 (after 0 or more iterations)
    ctx.push_assume("i_range", "i >= 0");

    // If i > 0, then the invariant "i == 0" should fail
    // So we add a disjunction: either i == 0 OR the invariant fails
    // For this test, we specifically want to check the case where i != 0
    ctx.push_assume("i_not_zero", "i > 0");

    // Invalid invariant that should fail when i > 0
    ctx.push_assert("invalid_invariant", "i == 0");

    // Verify with ay
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid invariant (i == 0 after increment) should fail, got: {:?}",
        result
    );
}

#[test]
fn test_decreases_measure_with_working_pattern() {
    // Test loop termination with decreases measure
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("n", "i32");
    ctx.declare_var_parsed("n_next", "i32");

    // Loop condition: n > 0
    ctx.push_assume("loop_condition", "n > 0");

    // Loop body: n decreases by 1
    ctx.push_assume("loop_decrement", "n_next == n - 1");

    // Termination check: measure decreases and stays non-negative
    ctx.push_assert("measure_decreases", "n_next < n && n_next >= 0");

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Decreasing measure should verify, got: {:?}",
        result
    );
}

#[test]
fn test_precondition_postcondition_pattern() {
    // Test function contract verification
    let mut ctx = VerificationContext::new();

    // Declare function parameter and result
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("result", "i32");

    // Precondition: x >= 0 and guard against overflow
    // For i32, MAX_INT is 2147483647, so x must be < MAX_INT to avoid overflow
    ctx.push_assume("precondition", "x >= 0 && x < 2147483647");

    // Function body: result = x + 1
    ctx.push_assume("function_body", "result == x + 1");

    // Postcondition: result > x
    ctx.push_assert("postcondition", "result > x");

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Postcondition should verify given precondition, got: {:?}",
        result
    );
}

#[test]
fn test_array_bounds_with_working_pattern() {
    // Test array bounds: assume i >= 0, i < len, then assert i + 1 <= len.
    // The assertion is a derived property (not a restatement of assumptions).
    // Requires solver to reason: i < len ⟹ i + 1 ≤ len.
    // (#1595: was asserting i >= 0 && i < len, the exact conjunction of assumptions)
    let mut ctx = VerificationContext::new();

    // Declare array index and length
    ctx.declare_var_parsed("i", "i32");
    ctx.declare_var_parsed("len", "i32");

    // Assumptions: array has positive length, index is within bounds
    ctx.push_assume("positive_length", "len > 0");
    ctx.push_assume("lower_bound", "i >= 0");
    ctx.push_assume("upper_bound", "i < len");

    // Derived property: i < len implies i + 1 <= len
    ctx.push_assert("next_index_bound", "i + 1 <= len");

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "i < len implies i + 1 <= len should verify, got: {:?}",
        result
    );
}

#[test]
fn test_multiple_assertions_pattern() {
    // Test that multiple assertions can be verified together
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Assumptions with bounds to prevent overflow
    ctx.push_assume("x_positive", "x > 0 && x < 1000000");
    ctx.push_assume("y_greater", "y > x && y < 1000000");

    // Multiple assertions that should all hold
    ctx.push_assert("x_nonzero", "x != 0");
    ctx.push_assert("y_positive", "y > 0");
    ctx.push_assert("sum_positive", "x + y > 0");

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "All assertions should verify given the assumptions, got: {:?}",
        result
    );
}
