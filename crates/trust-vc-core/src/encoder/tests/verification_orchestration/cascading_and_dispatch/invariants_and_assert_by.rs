// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Two loop invariants where the second depends on the first being assumed.
///
/// Tests verify_legacy (mod.rs:155-224): after verifying invariant #1,
/// it's added to verified_invariant_conditions and available as an
/// assumption when verifying invariant #2.
///
/// Invariant 1: x >= 0 (tautological for u32)
/// Invariant 2: x >= 0 && y >= 0 (tautological for u32, but exercises accumulation)
#[test]
fn test_cascading_loop_invariants_accumulate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_nonneg", "x >= 0",
        ));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "y_nonneg", "y >= 0",
        ));
    ctx.push_obligation(ProofObligation::assert("both_nonneg", "x >= 0 && y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cascading unsigned invariants should all verify");
}

/// Two loop invariants: first passes, second fails inductive step.
///
/// Tests that the pipeline stops at the failing invariant and returns
/// the correct counterexample, including the "inductive step" annotation.
#[test]
fn test_cascading_invariants_second_fails_inductive_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 42"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_nonneg", "x >= 0",
        ));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "y_exact", "y == 42",
        ));
    ctx.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "y == 42 should fail inductive step in havoc-all mode",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("inductive step"),
            "Should mention 'inductive step', got: {}",
            obligation_name
        );
        assert!(
            obligation_name.contains("y_exact"),
            "Should name the failing invariant, got: {}",
            obligation_name
        );
    }
}

/// Two assert_by obligations where the second uses the first's proven conclusion.
///
/// Tests verify_legacy (mod.rs:232-272): after verifying assert_by #1,
/// its conclusion is added to verified_assert_by and passed as an
/// assumption when verifying assert_by #2.
///
/// Assert-by #1: prove x > 0 (from assumption x == 5)
/// Assert-by #2: prove x > 0 && y > 0 (uses x > 0 from #1 + assumption y == 3)
#[test]
fn test_assert_by_conclusion_cascades() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("known_y", "y == 3"));

    ctx.add_assert_by(
        "prove_x_pos",
        "x > 0",
        vec![crate::vc::ProofObligation::assume("scope_helper", "x == 5")],
    );
    ctx.add_assert_by(
        "prove_y_pos",
        "y > 0",
        vec![crate::vc::ProofObligation::assume(
            "scope_helper2",
            "y == 3",
        )],
    );
    ctx.push_obligation(ProofObligation::assert("both_pos", "x > 0 && y > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Both assert_by conclusions should cascade to final assertion",
    );
}

/// Assert-by scoped assumptions do not leak to subsequent assert_by obligations.
///
/// Tests the scope isolation in verify_legacy (mod.rs:236-240): scoped
/// assumptions from assert_by #1 must not be visible in assert_by #2.
#[test]
fn test_assert_by_scoped_assumptions_do_not_leak() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));

    ctx.add_assert_by(
        "first_proof",
        "x > 0",
        vec![crate::vc::ProofObligation::assume("scope_z", "z == 99")],
    );
    ctx.add_assert_by("second_proof", "z == 99", vec![]);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Scoped z == 99 from first assert_by should not leak to second",
    );
}

/// Frame condition on unmodified variable preserves its value across iterations.
///
/// Setup: x modified, limit unmodified. Invariant: limit > 0.
/// Since limit is unmodified, frame condition gives limit == limit__trust_vc_pre.
/// Combined with pre-state invariant assumption (limit__trust_vc_pre > 0),
/// the post-state limit > 0 is proven through the frame equality.
#[test]
fn test_frame_condition_preserves_unmodified_relational_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("limit", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 100"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "limit_pos",
            "limit > 0",
        ));
    ctx.set_loop_modified_vars("limit_pos", vec!["x".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "limit > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Unmodified limit > 0 should verify via frame condition",
    );
}

/// Same setup as above but WITHOUT the loop guard — should fail inductive step.
///
/// Control test: without the guard, x is havoced and unconstrained (besides
/// being u32), so x < 100 can be false (x could be >= 100).
#[test]
fn test_frame_condition_without_guard_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("limit", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 100"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_bounded",
            "x < 100",
        ));
    ctx.set_loop_modified_vars("x_bounded", vec!["x".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "x < 100"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Without loop guard, x is havoced u32 so x < 100 can fail",
    );
}
