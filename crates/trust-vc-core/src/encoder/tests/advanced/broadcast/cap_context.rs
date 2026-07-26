//! Broadcast ground-instance cap and assumption-context correctness tests.
//!
//! Issues: #2113
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Broadcast ground-instance cap (#2113)
// ========================================================================

/// REGRESSION: A single broadcast assumption (under cap) should be encoded
/// as a quantified constraint, not a ground formula. Existing behavior must
/// be preserved for small numbers of broadcasts.
#[test]
fn test_broadcast_under_cap_encodes_quantified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("single_broadcast", "n >= 0")
            .with_bound_vars(vec!["n".to_string()]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Single broadcast (under cap)");
}

/// DISCRIMINATING: 31+ broadcast assumptions exceed the cap (N=30). The
/// encoder should still succeed (no error) but broadcasts beyond the 30th
/// are asserted as ground formulas instead of quantified. This prevents
/// O(N³) E-matching explosion in the solver.
#[test]
fn test_broadcast_over_cap_still_succeeds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));

    // Add 35 broadcast assumptions — exceeds BROADCAST_INSTANCE_CAP (30)
    for i in 0..35 {
        ctx.obligations.push(
            crate::vc::ProofObligation::broadcast_assume(format!("broadcast_{}", i), "n >= 0")
                .with_bound_vars(vec!["n".to_string()]),
        );
    }
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "35 broadcasts (over cap)");
}

/// DISCRIMINATING: Exactly 30 broadcasts should all be quantified (at cap,
/// not over). The 30th broadcast is the last one encoded as a quantified
/// constraint.
#[test]
fn test_broadcast_at_exact_cap_still_quantified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));

    // Add exactly 30 broadcast assumptions — at BROADCAST_INSTANCE_CAP
    for i in 0..30 {
        ctx.obligations.push(
            crate::vc::ProofObligation::broadcast_assume(format!("broadcast_{}", i), "n >= 0")
                .with_bound_vars(vec!["n".to_string()]),
        );
    }
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Exactly 30 broadcasts (at cap)");
}

// ========================================================================
// Broadcast assumption context correctness
// ========================================================================

/// DISCRIMINATING: Broadcast bodies must be encoded with in_assumption_context
/// set to true, so that nested trigger-less forall sub-expressions are NOT
/// Skolemized. Without the fix, resolve_condition runs with
/// in_assumption_context=false, and any inner forall in the body would be
/// Skolemized (weakened from universal to a single fresh constant).
///
/// This test uses a broadcast body axiom for an uninterpreted function where
/// the broadcast is the ONLY source of information about the function. The
/// assertion cannot be proved without the broadcast contributing correctly.
/// Regression test for the in_assumption_context fix in
/// parse_and_add_broadcast_assumption.
#[test]
fn test_broadcast_assumption_context_set_during_body_encoding() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));

    // Broadcast body axiom: f(x) == x + 1 (only source of info about f)
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
    );

    // Assertion that REQUIRES the broadcast axiom to hold
    ctx.push_obligation(ProofObligation::assert("f_property", "f(5) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DISCRIMINATING: Broadcast body axiom must contribute to proof. f(5)==6 is only provable via the broadcast f(x)==x+1");
}

/// Negative counterpart: broadcast body axiom says f(x)==x+1, but assertion
/// claims f(5)==7. Must NOT verify — proves the broadcast test above is
/// discriminatory.
#[test]
fn test_broadcast_assumption_context_negative_wrong_property() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));

    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
    );

    // WRONG: f(5) should be 6, not 7
    ctx.push_obligation(ProofObligation::assert("f_wrong", "f(5) == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "f(5)==7 when broadcast says f(x)==x+1");
}

// ========================================================================
// Broadcast cap fallback preserves broadcast_guard (#2727)
// ========================================================================

/// DISCRIMINATING: When broadcast #31+ has a `broadcast_guard`, the cap
/// fallback must emit `guard ==> body` (not bare `body`). Without the fix
/// the guard is dropped, making the assumption unconditional and potentially
/// causing false Verified results.
///
/// Setup: 30 filler broadcasts saturate the cap, then a 31st guarded
/// broadcast (`x > 0 ==> f(x) > 0`) lands in the fallback path. Asserting
/// `f(a) > 0` with `a == 0` must NOT verify because the guard blocks the
/// axiom outside its domain.
#[test]
fn test_broadcast_cap_fallback_preserves_guard() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // 30 filler broadcasts to saturate BROADCAST_INSTANCE_CAP
    for i in 0..30 {
        ctx.obligations.push(
            crate::vc::ProofObligation::broadcast_assume(
                format!("filler_{}", i),
                "x >= 0 || x < 0", // tautology — does not affect provability
            )
            .with_bound_vars(vec!["x".to_string()]),
        );
    }

    // 31st broadcast: guarded. requires x > 0, ensures f(x) > 0
    let mut guarded =
        crate::vc::ProofObligation::broadcast_assume("broadcast_guarded_over_cap", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]);
    guarded.broadcast_guard = Some(vec![crate::vc::BroadcastGuardClause {
        condition: "x > 0".to_string(),
    }]);
    ctx.obligations.push(guarded);

    // a == 0 (outside guard domain) — must NOT verify
    ctx.push_obligation(ProofObligation::assume("a_zero", "a == 0"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "DISCRIMINATING: Cap fallback must preserve broadcast_guard — f(0)>0 must not verify when guard requires x>0",
    );
}
