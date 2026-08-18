// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_has_assertions() {
    let mut ctx = VerificationContext::new();

    // Empty context should have no assertions
    assert!(!ctx.has_assertions());

    // Adding an assumption shouldn't count as assertion
    ctx.push_obligation(ProofObligation::assume("precondition", "x > 0"));
    assert!(!ctx.has_assertions());

    // Adding an assertion should count
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));
    assert!(ctx.has_assertions());

    // Clear and test with Ensures
    ctx.obligations.clear();
    ctx.obligations
        .push(ProofObligation::ensures("postcondition", "result > 0"));
    assert!(ctx.has_assertions());

    // Requires is treated as an assumption in function body verification
    // (fixes #755, #1078) — it should NOT count as an assertion
    ctx.obligations.clear();
    ctx.obligations
        .push(ProofObligation::requires("requirement", "n >= 0"));
    assert!(!ctx.has_assertions()); // Requires is an assumption, not assertion

    // Test with only non-assertion obligations (only Assume)
    ctx.obligations.clear();
    ctx.obligations
        .push(ProofObligation::assume("assumption", "n >= 0"));
    assert!(!ctx.has_assertions());
}

#[test]
fn test_has_assumptions() {
    let mut ctx = VerificationContext::new();

    // Empty context should have no assumptions
    assert!(!ctx.has_assumptions());

    // Adding an assertion shouldn't count as assumption
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));
    assert!(!ctx.has_assumptions());

    // Adding Assume should count
    ctx.obligations.clear();
    ctx.push_obligation(ProofObligation::assume("precondition", "x > 0"));
    assert!(ctx.has_assumptions());

    // Requires should count as assumption
    ctx.obligations.clear();
    ctx.obligations
        .push(ProofObligation::requires("requirement", "n >= 0"));
    assert!(ctx.has_assumptions());

    // BroadcastAssume should count as assumption
    ctx.obligations.clear();
    ctx.obligations.push(ProofObligation::broadcast_assume(
        "broadcast",
        "forall x. f(x) >= 0",
    ));
    assert!(ctx.has_assumptions());

    // MeasureNonNegative should NOT count as assumption
    ctx.obligations.clear();
    ctx.add_measure_nonneg("n");
    assert!(!ctx.has_assumptions());

    // MeasureDecreases should NOT count as assumption
    ctx.obligations.clear();
    ctx.add_measure_decreases("n", "n_old", "n_new");
    assert!(!ctx.has_assumptions());

    // Ensures should NOT count as assumption
    ctx.obligations.clear();
    ctx.obligations
        .push(ProofObligation::ensures("postcondition", "result > 0"));
    assert!(!ctx.has_assumptions());
}

#[test]
fn test_has_assertions_with_measure_obligations() {
    // MeasureNonNegative and MeasureDecreases should count as assertions
    let mut ctx = VerificationContext::new();

    ctx.add_measure_nonneg("n");
    assert!(ctx.has_assertions());

    ctx.obligations.clear();
    ctx.add_measure_decreases("n", "n_old", "n_new");
    assert!(ctx.has_assertions());

    // BroadcastAssume should NOT count as assertion
    ctx.obligations.clear();
    ctx.obligations.push(ProofObligation::broadcast_assume(
        "broadcast",
        "forall x. f(x) >= 0",
    ));
    assert!(!ctx.has_assertions());
}

#[test]
fn test_typed_obligation_retains_expr_payload_and_origin() {
    let expr = crate::ir::TrustVcExpr::BoolLit(true);
    let obligation = ProofObligation::new_typed("typed_true", expr.clone(), ObligationKind::Assert);

    assert_eq!(obligation.condition(), "<typed:typed_true>");
    assert_eq!(
        obligation.condition_origin(),
        ConditionOrigin::TypedTrustVcExpr
    );
    assert_eq!(obligation.typed_expr(), Some(&expr));

    let mut ctx = VerificationContext::from_typed_parts(
        Vec::new(),
        vec![TypedProofObligation::assert("typed_true", expr)],
    );
    assert!(ctx.has_assertions());
    assert_eq!(
        ctx.obligations()[0].condition_origin(),
        ConditionOrigin::TypedTrustVcExpr
    );
    assert!(ctx.obligations()[0].typed_expr().is_some());

    ctx.obligations.clear();
    assert!(!ctx.has_assertions());
}

#[test]
fn source_catalog_math_int_context_defaults_false_for_all_public_constructors() {
    let ordinary = ProofObligation::new("ordinary", "x + x", ObligationKind::Assert);
    let typed = ProofObligation::new_typed(
        "typed",
        crate::ir::TrustVcExpr::BoolLit(true),
        ObligationKind::Assert,
    );

    assert!(!ordinary.source_catalog_math_int_context);
    assert!(!typed.source_catalog_math_int_context);
}
