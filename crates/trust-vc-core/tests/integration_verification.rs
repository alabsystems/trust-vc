//! End-to-end integration tests for the verification pipeline.
//!
//! These tests verify that the complete flow from trust_vc macros to ay solver
//! works correctly, including both positive tests (valid properties pass) and
//! negative tests (invalid properties are rejected).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::{ObligationKind, ProofObligation};
use trust_vc_core::verify_macro::{collect_obligation, verify_collected};
use trust_vc_core::VerifyResult;

/// Test that a simple valid property verifies successfully.
#[test]
fn test_valid_property_verifies() {
    common::with_clean_verification(|| {
        // The encoder expects simple expressions, not formal logic syntax
        // This tests a concrete property rather than a quantified one
        collect_obligation(
            ObligationKind::Assert,
            "identity_law".to_string(),
            "5 + 0 == 5".to_string(), // Concrete instance of identity law
            Some("test:26:1".to_string()),
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Identity law (5 + 0 == 5) should verify, got: {:?}",
            result
        );
    })
}

/// Test that an invalid property is rejected with a counterexample.
#[test]
fn test_invalid_property_rejected() {
    common::with_clean_verification(|| {
        // Simulate an invalid property - this should fail
        collect_obligation(
            ObligationKind::Assert,
            "invalid_claim".to_string(),
            "5 > 10".to_string(), // False! 5 is not greater than 10
            Some("test:59:1".to_string()),
        );

        let result = verify_collected();
        // 5 > 10 is false, should produce counterexample
        // obligation_name includes location suffix when location is provided (#1540)
        assert!(
            matches!(result, VerifyResult::Counterexample { ref obligation_name, .. } if obligation_name.starts_with("invalid_claim")),
            "Invalid property (5 > 10) should produce counterexample, got: {:?}",
            result
        );
    })
}

/// Test preconditions and postconditions together.
#[test]
fn test_requires_ensures_interaction() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare the variable first
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add a precondition (assumption)
    ctx.push_obligation(ProofObligation::assume("precondition", "x > 0"));

    // Add upper bound to prevent overflow in x + 1
    ctx.push_obligation(ProofObligation::assume(
        "overflow_prevention",
        "x < 2147483647",
    ));

    // Add a postcondition that follows from the precondition
    ctx.push_obligation(ProofObligation::assert("postcondition", "x + 1 > 1"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Postcondition should follow from precondition, got: {:?}",
        result
    );
}

/// Test that contradictory assumptions are detected.
#[test]
fn test_contradictory_assumptions_detected() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare variable
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add contradictory assumptions
    ctx.push_obligation(ProofObligation::assume("assume1", "x > 5"));
    ctx.push_obligation(ProofObligation::assume("assume2", "x < 3"));

    // Any assertion should now be provable (principle of explosion)
    ctx.push_obligation(ProofObligation::assert("anything", "0 == 1"));

    let result = ctx.verify();
    // Vacuous truth detection (#2258): contradictory assumptions are caught,
    // returning Unknown instead of silently verifying via explosion.
    assert!(
        matches!(result, VerifyResult::Unknown { .. }),
        "Contradictory assumptions should be caught by vacuous truth check, got: {:?}",
        result
    );
}

/// Test termination measure verification with symbolic variable.
///
/// Verifies the standard termination pattern: if n > 0, then n - 1 < n.
/// This exercises the SMT solver with a symbolic decrease check, unlike the
/// original test which only checked the constant `5 < 10`.
#[test]
fn test_termination_measure() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare symbolic variable for the termination argument
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Precondition: n > 0 (the recursive call guard)
    ctx.push_obligation(ProofObligation::assume("precondition", "n > 0"));

    // Termination measure: n - 1 < n (recursive call decreases the measure)
    ctx.push_obligation(ProofObligation::assert("decrease_check", "n - 1 < n"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Symbolic termination measure (n > 0 → n - 1 < n) should verify, got: {:?}",
        result
    );
}

/// Test collection type verification (Seq) with symbolic operations.
///
/// Exercises actual Seq encoding by using s.len() and s.index() in both
/// assumptions and assertions. The original test declared a Seq variable
/// but never referenced it — all assertions were on a separate integer.
#[test]
fn test_collection_types() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare a symbolic sequence
    ctx.declare_var_typed(
        "s",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("Seq<i32>"),
    );

    // Symbolic constraints on the sequence
    ctx.push_obligation(ProofObligation::assume("nonempty", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("first_positive", "s.index(0) > 0"));

    // Assert properties that follow from assumptions but require symbolic reasoning
    // through the Seq encoding (array theory in ay)
    ctx.push_obligation(ProofObligation::assert("length_positive", "s.len() > 0"));
    ctx.push_obligation(ProofObligation::assert("first_nonneg", "s.index(0) >= 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq symbolic properties should verify, got: {:?}",
        result
    );
}

/// Test that malformed expressions panic at collection time (#1723).
///
/// Expressions come from `stringify!()` in macro expansions and are always
/// valid Rust syntax. A parse failure indicates a bug in the macro system,
/// so `translate_rust_to_smt` panics with an unreachable invariant violation
/// rather than silently falling back.
#[test]
fn test_malformed_condition_handling() {
    // Clear state before test, then verify the panic
    trust_vc_core::verify_macro::clear_all_thread_locals();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        collect_obligation(
            ObligationKind::Assert,
            "malformed".to_string(),
            "(5 + 1 > 3".to_string(), // Missing closing ) — invalid Rust syntax
            Some("test:197:1".to_string()),
        );
    }));

    // Clean up thread-local state after panic
    trust_vc_core::verify_macro::clear_all_thread_locals();

    assert!(
        result.is_err(),
        "Malformed expression should panic per #1723 invariant"
    );
    let err = result.unwrap_err();
    let panic_msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .unwrap_or("");
    assert!(
        panic_msg.contains("#1723"),
        "Panic message should reference #1723 invariant, got: {}",
        panic_msg
    );
}

/// Test ObligationKind::Ensures with symbolic variable.
///
/// Verifies that an Ensures obligation works with symbolic reasoning:
/// given x > 5, the postcondition x > 0 should hold. The original test
/// only checked the constant `10 > 5`.
#[test]
fn test_ensures_obligation() {
    use trust_vc_core::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Declare symbolic variable
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Precondition: x > 5
    ctx.push_obligation(ProofObligation::assume("precondition", "x > 5"));

    // Postcondition (Ensures kind): x > 0 (weaker, follows from precondition)
    ctx.push_obligation(ProofObligation::ensures("postcondition", "x > 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Ensures obligation (x > 5 → x > 0) should verify symbolically, got: {:?}",
        result
    );
}

/// Test MeasureNonNegative with symbolic variable.
///
/// Verifies that the non-negativity measure check works symbolically:
/// given n > 0, verify n >= 0. The original test only checked `5 >= 0`.
#[test]
fn test_measure_nonneg_obligation() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare symbolic measure variable
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Precondition: n > 0
    ctx.push_obligation(ProofObligation::assume("precondition", "n > 0"));

    // Non-negativity check via MeasureNonNegative obligation kind
    ctx.add_measure_nonneg("n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "MeasureNonNegative (n > 0 → n >= 0) should verify symbolically, got: {:?}",
        result
    );
}

/// Test MeasureDecreases directly via VerificationContext.
///
/// Uses `add_measure_decreases_obligation` instead of `collect_obligation`
/// because MeasureDecreases requires measure semantics that the legacy string
/// translation path cannot encode (validation rejects it).
#[test]
fn test_measure_decreases_obligation() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.add_measure_decreases_obligation("measure_decreases", "3 < 5", None);

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "MeasureDecreases should verify when new < old, got: {:?}",
        result
    );
}

/// Test verification with more complex arithmetic expressions.
#[test]
fn test_complex_arithmetic_verification() {
    common::with_clean_verification(|| {
        // Test a more complex arithmetic property
        collect_obligation(
            ObligationKind::Assert,
            "complex_arithmetic".to_string(),
            "(2 * 3) + (4 - 1) == 9".to_string(), // 6 + 3 == 9, should be true
            Some("test:278:1".to_string()),
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Complex arithmetic should verify, got: {:?}",
            result
        );
    })
}

/// Test that MeasureDecreases correctly rejects false conditions.
///
/// Uses `add_measure_decreases_obligation` instead of `collect_obligation`
/// because MeasureDecreases requires measure semantics that the legacy string
/// translation path cannot encode (validation rejects it).
#[test]
fn test_measure_decreases_rejects_false() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.add_measure_decreases_obligation("invalid_decrease", "false", None);

    let result = ctx.verify();

    // Investigation in #735 confirmed: encoder correctly rejects false assertions
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "False should produce a counterexample, got: {:?}",
        result
    );
}

/// Test MeasureDecreases with symbolic variables.
///
/// Verifies that the decrease measure works symbolically:
/// given n > 0 and m == n - 1, verify m < n. The original test only
/// asserted the constant `true`.
#[test]
fn test_valid_measure_decreases() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare symbolic variables for old and new measure values
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("m", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Precondition: n > 0 and m is the recursive call argument (n - 1)
    ctx.push_obligation(ProofObligation::assume("precondition", "n > 0"));
    ctx.push_obligation(ProofObligation::assume("recursive_arg", "m == n - 1"));

    // Measure decrease: m < n (new measure is strictly less than old)
    ctx.add_measure_decreases_obligation("valid_decrease", "m < n", None);

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "MeasureDecreases (n > 0, m == n-1 → m < n) should verify symbolically, got: {:?}",
        result
    );
}

/// Test ObligationKind::Assume - assumptions are trusted and can be used to prove assertions.
#[test]
fn test_assume_obligation() {
    common::with_clean_verification(|| {
        // Assumptions are trusted, even if contradictory
        collect_obligation(
            ObligationKind::Assume,
            "assumption1".to_string(),
            "true".to_string(),
            Some("test:320:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "assumption2".to_string(),
            "false".to_string(), // Contradicts the first assumption (true && false = false)
            Some("test:327:1".to_string()),
        );

        // Add an assertion that tests the behavior with contradictory assumptions
        // With contradictory assumptions (true && false), the context is unsatisfiable
        collect_obligation(
            ObligationKind::Assert,
            "test_assert".to_string(),
            "1 == 2".to_string(), // This absurd claim should be provable from contradictions
            Some("test:336:1".to_string()),
        );

        // Vacuous truth detection (#2258): contradictory assumptions are caught
        let result = verify_collected();
        // Contradictory assumptions (true && false) make context UNSAT.
        // Vacuous truth check returns Unknown instead of silently verifying.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Contradictory assumptions should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

/// Test ObligationKind::Requires - preconditions are assumptions at function entry.
#[test]
fn test_requires_obligation() {
    use trust_vc_core::vc::VerificationContext;

    let mut ctx = VerificationContext::new();

    // Declare the variable first
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Requires acts as an assumption for the function body
    ctx.push_obligation(ProofObligation::assume("precondition", "n >= 0"));

    // Add upper bound to prevent overflow in n + 1
    ctx.push_obligation(ProofObligation::assume(
        "overflow_prevention",
        "n < 2147483647",
    ));

    // With the precondition, we can verify a property that depends on it
    ctx.push_obligation(ProofObligation::assert("derived_property", "n + 1 > 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "With precondition n >= 0, property n + 1 > 0 should verify, got: {:?}",
        result
    );
}
