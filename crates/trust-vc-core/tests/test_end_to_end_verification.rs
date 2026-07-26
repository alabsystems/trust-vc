//! End-to-end verification tests for trust_vc
//! These tests demonstrate actual verification working with ay solver
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

use trust_vc_core::vc::{ObligationKind, ProofObligation, VerificationContext};
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

fn obligation(
    name: &str,
    condition: &str,
    kind: ObligationKind,
    location: &str,
) -> ProofObligation {
    ProofObligation::new(name, condition, kind).with_location(location)
}

/// Test 1: Basic proof verification - valid assertion
#[test]
fn test_proof_valid_assertion() {
    common::with_clean_verification(|| {
        // Simulate: trust_vc::assert!(a + b >= a) for u32 types
        // In ay encoding: forall a, b: u32. a + b >= a
        // This is valid because u32 addition saturates at max
        collect_obligation(
            ObligationKind::Assert,
            "valid_addition".to_string(),
            "10 + 5 >= 10".to_string(), // Concrete example: 15 >= 10 is true
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid assertion (10 + 5 >= 10) should verify, got: {:?}",
            result
        );
    })
}

/// Test 2: Basic proof verification - invalid assertion
#[test]
fn test_proof_invalid_assertion() {
    common::with_clean_verification(|| {
        // Simulate: trust_vc::assert!(5 < 3)
        // This is obviously false
        collect_obligation(
            ObligationKind::Assert,
            "invalid_comparison".to_string(),
            "5 < 3".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invalid assertion (5 < 3) should return counterexample, got: {:?}",
            result
        );
    })
}

/// Test 3: Termination checking - valid decreases
/// Uses VerificationContext directly because MeasureDecreases/MeasureNonNegative
/// are rejected by the legacy string validation boundary (validation.rs, #2725).
#[test]
fn test_termination_valid_decreases() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(obligation(
        "factorial_decreases",
        "5 - 1 < 5",
        ObligationKind::MeasureDecreases,
        "test:1:1",
    ));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Valid termination (n-1 < n) should verify, got: {:?}",
        result
    );
}

/// Test 4: Termination checking - invalid increases
/// See Test 3 comment on MeasureDecreases + VerificationContext.
#[test]
fn test_termination_invalid_increases() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(obligation(
        "infinite_loop_increases",
        "5 + 1 < 5",
        ObligationKind::MeasureDecreases,
        "test:1:1",
    ));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Invalid termination (n+1 < n) should return counterexample, got: {:?}",
        result
    );
}

/// Test 5: Proof with assumptions using symbolic variable
/// (#1595: was all-concrete "5 > 0" / "5 + 1 > 1" — trivially true without solver reasoning)
#[test]
fn test_proof_with_assumptions() {
    common::with_clean_verification(|| {
        // Use a symbolic variable so the solver must reason about the assumption
        collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 0 with overflow guard
        collect_obligation(
            ObligationKind::Assume,
            "value_positive".to_string(),
            "x > 0 && x < 2147483647".to_string(),
            Some("test:1:1".to_string()),
        );

        // Assert derived property: x + 1 > 1 (requires: x > 0 ⟹ x + 1 > 1)
        collect_obligation(
            ObligationKind::Assert,
            "derived_property".to_string(),
            "x + 1 > 1".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 implies x + 1 > 1 should verify, got: {:?}",
            result
        );
    })
}

/// Test 6: End-to-end with actual VerificationContext
#[test]
fn test_end_to_end_with_context() {
    let mut ctx = VerificationContext::new();

    // Add a simple assertion
    ctx.push_obligation(obligation(
        "e2e_test",
        "2 + 2 == 4",
        ObligationKind::Assert,
        "test:1:1",
    ));

    // Verify using ay
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Simple arithmetic (2 + 2 == 4) should verify, got: {:?}",
        result
    );
}

/// Test 7: Minimal assertion — verifies "true" through the collect→verify pipeline
#[test]
fn test_assert_true_verifies() {
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Assert,
            "assert_true".to_string(),
            "true".to_string(),
            Some("test:1:1".to_string()),
        );
        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Asserting 'true' should verify, got: {:?}",
            result
        );
    })
}

/// Test 8: Complex arithmetic expressions
#[test]
fn test_complex_arithmetic() {
    common::with_clean_verification(|| {
        // Test distributive property: 2 * (3 + 4) == 2 * 3 + 2 * 4
        collect_obligation(
            ObligationKind::Assert,
            "distributive".to_string(),
            "2 * (3 + 4) == 2 * 3 + 2 * 4".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Distributive property should verify, got: {:?}",
            result
        );
    })
}

/// Test 9: Measure non-negative check
/// See Test 3 comment on MeasureDecreases + VerificationContext.
#[test]
fn test_measure_non_negative() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(obligation(
        "measure_positive",
        "5 >= 0",
        ObligationKind::MeasureNonNegative,
        "test:1:1",
    ));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Non-negative measure (5 >= 0) should verify, got: {:?}",
        result
    );
}

/// Test 10: Ensures (postcondition) verification
#[test]
fn test_ensures_postcondition() {
    common::with_clean_verification(|| {
        // Simulate a function that ensures result > input
        // We'll use concrete values to test
        collect_obligation(
            ObligationKind::Ensures,
            "result_greater".to_string(),
            "10 > 5".to_string(), // Result 10 > input 5
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid postcondition (10 > 5) should verify, got: {:?}",
            result
        );
    })
}

/// Test 11: Requires (precondition) verification with symbolic variable
/// (#1595: was all-concrete "10 > 0" / "10 + 1 > 1" — trivially true without solver reasoning)
#[test]
fn test_requires_precondition() {
    let mut ctx = VerificationContext::new();

    // Use a symbolic variable so the solver must reason through the requires
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Requires: x > 0 with overflow guard (acts as assumption in callee-side verification)
    // BV semantics: x + 1 wraps at i32::MAX, so we must guard against overflow
    ctx.push_obligation(obligation(
        "input_positive",
        "x > 0 && x < 2147483647",
        ObligationKind::Requires,
        "test:1:1",
    ));

    // Assert derived property: x + 1 > 1 (requires: x > 0 && no overflow ⟹ x + 1 > 1)
    ctx.push_obligation(obligation(
        "derived",
        "x + 1 > 1",
        ObligationKind::Assert,
        "test:2:1",
    ));

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "requires(x > 0 && x < MAX) should imply x + 1 > 1, got: {:?}",
        result
    );
}
