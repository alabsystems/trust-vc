//! Recommends clause — soft precondition verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for ObligationKind::Recommends: it is ADVISORY — a soft-warning check,
//! NEVER a hard assumption. At call sites violations produce warnings, not
//! failures. At body level it is NOT assumed (assuming it was a false-verify —
//! a function's own recommends let a false ensures/assert verify; fixed
//! 2026-07-24, prepared_context/validation.rs).
//!
//! Part of #2483.

use super::*;

/// Recommends satisfied at call site: x > 0 with x > 5 assumed.
/// Should verify without failure.
#[test]
fn test_recommends_satisfied_at_call_site() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 5"));
    ctx.obligations
        .push(ProofObligation::recommends("rec_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "recommends satisfied should verify");
}

/// Recommends violated at call site: recommends(x > 0) but only x > -10.
/// Should still return Verified (warnings only, not failure).
#[test]
fn test_recommends_violated_returns_verified() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x > -10"));
    ctx.obligations
        .push(ProofObligation::recommends("rec_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "recommends violation should still return Verified (warning only)",
    );
}

/// CARDINAL: Recommends at body level is ADVISORY, NOT an assumption. A
/// function's own `recommends(x > 0)` must NOT be assumed when proving the body,
/// so an `assert(x > 0)` with `x` otherwise unconstrained must FAIL. Assuming it
/// was a false-verify (`#[recommends(x==0)] #[ensures(result==0)] fn f(x){x}`
/// verified). Fixed 2026-07-24.
#[test]
fn test_recommends_body_level_not_assumed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations
        .push(ProofObligation::recommends("rec_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("x_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "CARDINAL: recommends at body level must NOT be assumed — `assert(x > 0)` with x \
         unconstrained must not verify from an advisory recommends",
    );
}

/// Recommends with regular requires: both should work together.
/// Requires is checked as assertion at call site; recommends is warning-only.
#[test]
fn test_recommends_and_requires_combined() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 5"));
    ctx.obligations
        .push(ProofObligation::requires("req_bounded", "x > 0"));
    ctx.obligations
        .push(ProofObligation::recommends("rec_small", "x < 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "requires satisfied + recommends satisfied should verify",
    );
}

/// Recommends does not affect a failing regular assertion.
/// A real assertion failure should still produce Counterexample.
#[test]
fn test_recommends_no_effect_on_assertion_failure() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_negative", "x < 0"));
    ctx.obligations
        .push(ProofObligation::requires("req_positive", "x > 0"));
    ctx.obligations
        .push(ProofObligation::recommends("rec_bounded", "x < 100"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "requires failure should still produce counterexample despite recommends",
    );
}
