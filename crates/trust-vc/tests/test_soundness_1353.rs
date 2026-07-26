// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for issue #1353: Invalid decreases measures verify as correct
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid termination measures
//!
//! This test suite is critical for ensuring the verification system is sound.
//! Each test MUST produce a counterexample or Unknown result for invalid code.
//! If any of these tests produce Verified, we have a soundness bug.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

#[test]
fn test_soundness_invalid_decreases_increasing() {
    // Test that a measure that increases instead of decreases is rejected
    let mut ctx = VerificationContext::new();

    // Declare variables for the recursion
    ctx.declare_var_parsed("n", "u64");

    // Add an invalid decreases obligation: n+1 < n is always false for u64
    // This simulates: #[decreases(n)] fn bad_recurse(n: u64) { bad_recurse(n + 1); }
    ctx.add_measure_decreases_obligation(
        "invalid_increasing_measure",
        "(n + 1) < n", // This is ALWAYS FALSE for u64
        Some("test_soundness_1353.rs:27".to_string()),
    );

    // Verify the context
    let result = ctx.verify();

    // (n + 1) < n is always false for BV — ay must find counterexample.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid increasing measure should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_soundness_invalid_decreases_same_value() {
    // Test that a measure with the same value (non-decreasing) is rejected
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("n", "u64");

    // Add an invalid decreases obligation: n < n is always false
    ctx.add_measure_decreases_obligation(
        "invalid_same_value_measure",
        "n < n", // This is ALWAYS FALSE
        Some("test_soundness_1353.rs:62".to_string()),
    );

    let result = ctx.verify();

    // n < n is trivially false — ay must find counterexample.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid same-value measure should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_soundness_invalid_decreases_multiply() {
    // Test that a measure that multiplies (and thus increases) is rejected
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("n", "u64");

    // Add an assumption that n > 1 (to make multiplication increase)
    ctx.push_assume("n_gt_1", "n > 1");

    // Add an invalid decreases obligation: n*2 < n is false when n > 1
    ctx.add_measure_decreases_obligation(
        "invalid_multiply_measure",
        "(n * 2) < n", // This is FALSE when n > 1
        Some("test_soundness_1353.rs:100".to_string()),
    );

    let result = ctx.verify();

    // With n > 1, n*2 < n is false (no BV overflow since n*2 > n for small n,
    // and for large n the overflow makes n*2 < n only when n is very large,
    // but ay should still find a counterexample in the common case).
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid multiply measure should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_soundness_invalid_decreases_concrete_values() {
    // Test with concrete values to avoid solver complexity
    let mut ctx = VerificationContext::new();

    // Test that 6 < 5 is false (simulating recursion with n=5 calling with n+1=6)
    ctx.add_measure_decreases_obligation(
        "invalid_concrete_increase",
        "6 < 5", // This is ALWAYS FALSE
        Some("test_soundness_1353.rs:135".to_string()),
    );

    let result = ctx.verify();

    // 6 < 5 is a trivially false constant — must produce counterexample.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid concrete measure (6 < 5) should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_valid_decreases_should_verify() {
    // Control test: valid decreases measures SHOULD verify
    let mut ctx = VerificationContext::new();

    // Test that 4 < 5 is true (simulating valid recursion with n=5 calling with n-1=4)
    ctx.add_measure_decreases_obligation(
        "valid_concrete_decrease",
        "4 < 5", // This is TRUE
        Some("test_soundness_1353.rs:167".to_string()),
    );

    // Verify the context
    let result = ctx.verify();

    // This SHOULD verify - if it doesn't, our verification is broken
    match result {
        VerifyResult::Verified => {
            // Good! Valid measure verified correctly
        }
        _ => {
            panic!("Valid decreases measure failed to verify: {:?}", result);
        }
    }
}
