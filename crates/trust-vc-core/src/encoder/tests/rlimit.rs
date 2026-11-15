//! Per-function rlimit — solver timeout override tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for `VerificationContext::set_rlimit(ms)`: per-function solver timeout
//! override that flows through `PreparedVerificationContext` to `setup_from_prepared`.
//!
//! Part of #2489.

use super::*;
use std::time::Duration;

/// Default rlimit (no override): a trivially satisfiable assertion verifies
/// normally with the default 30,000ms timeout.
#[test]
fn test_rlimit_default_when_absent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("x_pos_check", "x > 0"));

    // No set_rlimit call — uses default 30,000ms
    assert!(
        ctx.rlimit_ms.is_none(),
        "rlimit_ms should be None by default"
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "default rlimit should verify trivial assertion");
}

/// Generous rlimit: a simple assertion with a large rlimit should verify fine.
#[test]
fn test_rlimit_generous_verifies_normally() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x > 5"));
    ctx.push_obligation(ProofObligation::assert("x_positive", "x > 0"));
    ctx.set_rlimit(60_000); // 60s — very generous

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "generous rlimit should verify simple assertion");
}

/// Rlimit flows through prepare_context to PreparedVerificationContext.
#[test]
fn test_rlimit_threads_through_prepare_context() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));
    ctx.set_rlimit(5_000);

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    assert_eq!(
        prepared.rlimit_ms,
        Some(5_000),
        "rlimit_ms should be threaded through prepare_context"
    );
}

/// Rlimit is None when not set.
#[test]
fn test_rlimit_none_threads_through_prepare_context() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    assert_eq!(
        prepared.rlimit_ms, None,
        "rlimit_ms should be None when not set"
    );
}

/// Rlimit does not affect verification correctness: the assertion result should
/// be the same regardless of rlimit (given sufficient time). Here we set a
/// moderate rlimit and verify a counterexample is still found.
#[test]
fn test_rlimit_does_not_affect_counterexample_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_negative", "x < 0"));
    ctx.push_obligation(ProofObligation::assert("x_positive", "x > 0"));
    ctx.set_rlimit(10_000); // 10s — more than enough for trivial query

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "rlimit should not prevent counterexample detection for falsifiable assertions",
    );
}

/// `setup_from_prepared` must apply the explicit rlimit to the fresh solver
/// instance it creates, not just preserve the value on PreparedVerificationContext.
#[test]
fn test_setup_from_prepared_applies_explicit_rlimit_to_solver_timeout() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));
    ctx.set_rlimit(1_234);

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    let slices =
        crate::encoder::verification::VerificationSlices::new(&prepared, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should succeed");

    assert_eq!(
        encoder.solver.timeout(),
        Some(Duration::from_millis(1_234)),
        "setup_from_prepared should apply the explicit rlimit to the solver"
    );
}

/// Absent an rlimit override, `setup_from_prepared` installs the default wall
/// from [`crate::encoder::verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS`]
/// — read from the constant, not restated, because that number is the whole
/// envelope (search AND ay's certification funnel) and it moved once already.
#[test]
fn test_setup_from_prepared_uses_default_solver_timeout_without_rlimit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    let slices =
        crate::encoder::verification::VerificationSlices::new(&prepared, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should succeed");

    assert_eq!(
        encoder.solver.timeout(),
        Some(Duration::from_millis(
            crate::encoder::verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS
        )),
        "setup_from_prepared should use the default wall when no rlimit is set"
    );
}
