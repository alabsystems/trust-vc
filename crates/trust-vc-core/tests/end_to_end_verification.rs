// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end verification tests demonstrating actual ay verification

mod common;

use trust_vc_core::vc::{ObligationKind, ProofObligation, VerificationContext};
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

/// Test that valid arithmetic properties are verified by ay
#[test]
fn test_e2e_valid_arithmetic_verified() {
    let mut ctx = VerificationContext::new();

    // Declare variables with bounded values to avoid overflow
    ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));

    // Add assumption that values are small enough to avoid overflow
    // u32::MAX is 4294967295, so if a + b <= u32::MAX, no overflow occurs
    ctx.push_obligation(ProofObligation::assume("bounded_a", "a <= 2147483647")); // a <= (u32::MAX / 2)
    ctx.push_obligation(ProofObligation::assume("bounded_b", "b <= 2147483647")); // b <= (u32::MAX / 2)

    // Property: a + b >= a (holds when no overflow)
    ctx.push_obligation(ProofObligation::assert("addition_monotonic", "a + b >= a"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Valid property a + b >= a should verify, got: {:?}",
        result
    );
}

/// Test that invalid properties are rejected with counterexample
#[test]
fn test_e2e_invalid_property_counterexample() {
    let mut ctx = VerificationContext::new();

    // Use symbolic variable so ay must reason about the property
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Invalid property: x + 1 < x (false for any non-overflowing x)
    ctx.push_obligation(ProofObligation::assume(
        "bounded",
        "x >= 0 && x < 2147483646",
    ));
    ctx.push_obligation(ProofObligation::assert("false_property", "x + 1 < x"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid property x + 1 < x should produce counterexample, got: {:?}",
        result
    );
}

/// Test that termination measure decrease is verified with symbolic reasoning
#[test]
fn test_e2e_valid_termination_verified() {
    common::with_clean_verification(|| {
        // Use symbolic variable so ay must actually reason about the measure
        collect_variable("n".to_string(), "u64".to_string());

        // Assume n > 0 so (n - 1) is valid and < n
        collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // MeasureDecreases: (n - 1) < n should verify when n > 0
        collect_obligation(
            ObligationKind::MeasureDecreases,
            "factorial_decreases".to_string(),
            "(n - 1) < n".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid termination measure (n - 1) < n with n > 0 should verify, got: {:?}",
            result
        );
    })
}

/// Test that invalid termination (increasing measure) is rejected
#[test]
fn test_e2e_invalid_termination_rejected() {
    common::with_clean_verification(|| {
        // Simulate infinite loop: n increases to n+1
        collect_variable("n".to_string(), "u64".to_string());

        // Check that measure decreases: (n + 1) < n (INVALID!)
        collect_obligation(
            ObligationKind::MeasureDecreases,
            "infinite_loop".to_string(),
            "(n + 1) < n".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invalid termination (n+1) < n should be rejected, got: {:?}",
            result
        );
    })
}

/// Test requires/ensures contract verification
#[test]
fn test_e2e_contract_verification() {
    common::with_clean_verification(|| {
        // Simulate: requires n > 0, ensures result > n
        collect_variable("n".to_string(), "u64".to_string());
        collect_variable("result".to_string(), "u64".to_string());

        // For contract verification, we need to assume the precondition holds
        // (In a real function call, the Requires would be verified at the call site)
        collect_obligation(
            ObligationKind::Assume,
            "precondition".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Add upper bound to prevent overflow
        // Note: Using i64::MAX as the encoder fails to parse decimal literals > i64::MAX
        collect_obligation(
            ObligationKind::Assume,
            "overflow_prevention".to_string(),
            "n < 9223372036854775807".to_string(), // i64::MAX (encoder limitation)
            None,
        );

        // Simulate computation: result = n + 1
        collect_obligation(
            ObligationKind::Assume,
            "computation".to_string(),
            "result == n + 1".to_string(),
            None,
        );

        // Postcondition as assertion
        collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "result > n".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid contract should verify, got: {:?}",
            result
        );
    })
}

/// Test that contradictory assumptions are detected as vacuous truth
#[test]
fn test_e2e_contradictory_assumptions_vacuous() {
    let mut ctx = VerificationContext::new();

    // Declare variable
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add contradictory assumptions
    ctx.push_obligation(ProofObligation::assume("assume1", "x > 5"));
    ctx.push_obligation(ProofObligation::assume("assume2", "x < 3"));

    // Any assertion should NOT silently verify via contradiction
    ctx.push_obligation(ProofObligation::assert("absurd", "1 == 2"));

    let result = ctx.verify();
    // Vacuous truth detection (#2258): contradictory assumptions (x > 5 && x < 3)
    // are caught before assertions run, returning Unknown instead of silently
    // verifying via principle of explosion.
    assert!(
        matches!(result, VerifyResult::Unknown { .. }),
        "Contradictory assumptions should be caught by vacuous truth check, got: {:?}",
        result
    );
}

/// Test complex arithmetic with multiple variables
#[test]
fn test_e2e_complex_arithmetic() {
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("z", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Assumptions with bounds to prevent overflow
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x > 0 && x <= 1073741823",
    )); // x <= (i32::MAX / 2)
    ctx.push_obligation(ProofObligation::assume(
        "y_bound",
        "y > 0 && y <= 1073741823",
    )); // y <= (i32::MAX / 2)
    ctx.push_obligation(ProofObligation::assume("sum", "z == x + y"));

    // Property to verify
    ctx.push_obligation(ProofObligation::assert("sum_positive", "z > 0"));

    let result = ctx.verify();

    // Bounded positive ints: x > 0, y > 0, z == x + y → z > 0.
    // With explicit overflow prevention bounds, ay-dpll verifies this.
    assert!(
        matches!(result, VerifyResult::Verified),
        "Sum of bounded positive numbers should verify, got: {:?}",
        result
    );
}

/// Test that measure non-negative obligations are checked
#[test]
fn test_e2e_measure_nonnegative() {
    common::with_clean_verification(|| {
        // Test with valid non-negative measure
        collect_variable("n".to_string(), "u64".to_string());

        collect_obligation(
            ObligationKind::MeasureNonNegative,
            "measure_nonneg".to_string(),
            "n >= 0".to_string(), // u64 is always >= 0
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "u64 >= 0 should always verify, got: {:?}",
            result
        );
    })
}

/// Test sequence length properties
#[test]
fn test_e2e_sequence_verification() {
    let mut ctx = VerificationContext::new();

    // Declare a sequence
    ctx.declare_var_typed(
        "s",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("Seq<i32>"),
    );

    // Property: length is non-negative
    ctx.push_obligation(ProofObligation::assert("seq_len_nonneg", "s.len() >= 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Sequence length >= 0 should verify, got: {:?}",
        result
    );
}

/// Integration test showing full proof workflow
#[test]
fn test_e2e_complete_proof_workflow() {
    common::with_clean_verification(|| {
        // Simulate a complete proof with variables, assumptions, and assertions
        collect_variable("n".to_string(), "i32".to_string());

        // Assumption: n is positive and bounded to prevent overflow
        collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0 && n < 2147483646".to_string(), // n < (i32::MAX - 1) to allow n+1
            None,
        );

        // Derive: n + 1 > 1
        collect_obligation(
            ObligationKind::Assert,
            "derived".to_string(),
            "n + 1 > 1".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Complete proof workflow should verify, got: {:?}",
            result
        );
    })
}
