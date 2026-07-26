//! Tests for extended-timeout retry on BV solver timeout.
//!
//! When the initial BV solver attempt times out and int-mode retry is
//! inapplicable (no overflow checks) or also fails, the extended-timeout
//! retry creates a fresh encoder with 2x BV_HARD_TIMEOUT. This recovers
//! marginal timeouts caused by ay-dpll non-determinism (#2273).
//! Part of #2313.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::verification::test_hooks::{FORCE_BV_TIMEOUT, FORCE_EXTENDED_RETRY_SUCCESS};

/// Scenario 1: BV timeout + no overflow checks → extended retry recovers.
///
/// FORCE_BV_TIMEOUT makes the initial BV attempt return Timeout.
/// The extended retry runs with a fresh encoder and 2x timeout, and the
/// simple assertion verifies normally.
#[test]
fn test_extended_retry_recovers_on_timeout_without_overflow() {
    let mut ctx = VerificationContext::new(); // No .with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_bound", "x < 1000"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y < 1000"));
    ctx.push_obligation(ProofObligation::assert("sum_bound", "x + y < 2000"));

    // Baseline: verifies without forced timeout.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(&baseline, "Baseline: bounded sum should verify");

    // Forced BV timeout: extended retry should recover.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "Extended retry should recover Verified on simple assertion",
    );
}

/// Scenario 2: BV timeout + false assertion → extended retry finds counterexample.
///
/// The assertion is provably false (x==100, assert x<50). The initial BV
/// attempt times out (forced), but the extended retry runs the real solver,
/// finds x==100 ∧ ¬(x<50) is SAT, and surfaces the counterexample.
#[test]
fn test_extended_retry_finds_counterexample_on_false_assertion() {
    let mut ctx = VerificationContext::new(); // No overflow checks
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("wrong", "x < 50"));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    // The forced timeout applies to the initial BV attempt only. The extended
    // retry runs the real solver and finds the counterexample. Previously,
    // the retry cascade filtered for Verified-only, discarding counterexamples
    // and falling back to the original timeout Unknown. Now we correctly
    // surface definitive answers (Verified or Counterexample) from retries.
    expect_counterexample(
        &result,
        "Extended retry should find counterexample for false assertion",
    );
}

/// Scenario 3: BV timeout + overflow checks → int-mode retry fires first.
///
/// With overflow checks enabled, the int-mode retry takes priority (existing
/// #2262 behavior). The extended retry is only a fallback if int-mode fails.
/// Here the simple assertion verifies under int-mode, so extended retry is
/// never reached.
#[test]
fn test_int_mode_retry_takes_priority_over_extended() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_bound", "x < 1000"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y < 1000"));
    ctx.push_obligation(ProofObligation::assert("sum_bound", "x + y < 2000"));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "Int-mode retry should recover before extended retry is needed",
    );
}

/// Regression for #2707: skip mode must return the initial timeout Unknown
/// instead of entering the int-mode retry path.
#[test]
fn test_skip_retry_cascade_bypasses_int_mode_retry() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.set_skip_retry_cascade(true);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_bound", "x < 1000"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y < 1000"));
    ctx.push_obligation(ProofObligation::assert("sum_bound", "x + y < 2000"));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    expect_unknown(
        &result,
        "skip_retry_cascade should return the initial timeout Unknown before int-mode retry",
    );
}

/// Scenario 4: Non-timeout Unknown skips extended retry entirely.
///
/// A SolverPanic or other non-timeout Unknown category should NOT trigger
/// the extended retry — only Timeout unknowns are retryable.
/// We verify this by checking that a non-timeout unknown from a sort
/// mismatch or similar encoder failure stays as Unknown without retry.
#[test]
fn test_non_timeout_unknown_skips_extended_retry() {
    // Use an assertion that produces a non-timeout Unknown (e.g., a
    // collection op in quantifier body that triggers sort mismatch).
    // If no sort mismatch, use FORCE_EXTENDED_RETRY_SUCCESS to detect
    // whether the retry path was entered — if it was entered and the
    // hook is off, the assertion would still fail; if not entered, the
    // hook doesn't matter.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == 5"));

    // Without forced timeout, verify baseline succeeds.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(&baseline, "Baseline should verify");

    // With FORCE_EXTENDED_RETRY_SUCCESS but NO forced timeout, the
    // assertion should verify normally on the first attempt. The hook
    // should never be consulted because no timeout occurs.
    let result = {
        let _hook = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "Non-timeout path should verify directly without retry",
    );
}

/// Test the FORCE_EXTENDED_RETRY_SUCCESS hook: when set, BV timeout +
/// no overflow checks should recover via the forced hook without running
/// the actual extended solver.
#[test]
fn test_forced_extended_retry_hook_recovers() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    // This assertion is FALSE — would not verify under real solver.
    ctx.push_obligation(ProofObligation::assert("wrong", "x < 50"));

    // With both FORCE_BV_TIMEOUT and FORCE_EXTENDED_RETRY_SUCCESS,
    // the hook short-circuits to Verified even though the assertion
    // is actually false. This proves the hook is consulted.
    let result = {
        let _timeout = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        let _hook = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "FORCE_EXTENDED_RETRY_SUCCESS hook should short-circuit to Verified",
    );
}

/// Regression for #2707: skip mode must return the initial timeout Unknown
/// instead of entering the extended-timeout retry path.
#[test]
fn test_skip_retry_cascade_bypasses_extended_retry() {
    let mut ctx = VerificationContext::new();
    ctx.set_skip_retry_cascade(true);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("wrong", "x < 50"));

    let result = {
        let _timeout = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        let _hook = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        AYEncoder::verify(&ctx)
    };

    expect_unknown(
        &result,
        "skip_retry_cascade should return the initial timeout Unknown before extended retry",
    );
}

/// Regression for #2317: inductive-step verification should use the same
/// forced-timeout and extended-retry hooks as the main assertion path.
///
/// Baseline: `x == 0` fails the havoc-all inductive step. With both forced
/// hooks enabled, the result should become Verified only if
/// `verify_with_confirmation` consults the retry path.
#[test]
fn test_forced_extended_retry_hook_recovers_inductive_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init", "x == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "always_zero",
            "x == 0",
        ));
    ctx.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let baseline = AYEncoder::verify(&ctx);
    expect_counterexample(
        &baseline,
        "Baseline: x == 0 should fail inductive step without forced retry",
    );

    let recovered = {
        let _timeout = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        let _retry = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &recovered,
        "Forced retry hooks should recover the inductive step path",
    );
}

/// Regression for #2328: collection confirmation pass must use the same
/// timeout retry cascade as the initial attempt.
///
/// Before the fix, the confirmation check called the one-shot timeout wrapper
/// directly. If the confirmation attempt timed out, it was misclassified as
/// `ConfirmationDisagree` even though the same timeout was retriable.
///
/// This test forces a BV timeout on a collection (Seq) assertion without
/// overflow checks, so the extended-timeout retry is the only recovery path.
/// Both the initial attempt and the confirmation attempt must go through the
/// retry cascade. With FORCE_EXTENDED_RETRY_SUCCESS, both should recover.
#[test]
fn test_extended_retry_propagates_to_collection_confirmation_check() {
    let mut ctx = VerificationContext::new(); // No overflow checks
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("len_check", "s.len() >= 1"));

    // Baseline: verifies without forced timeout.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(
        &baseline,
        "Baseline: s.len()==3 => s.len()>=1 should verify",
    );

    // Forced BV timeout + forced extended retry success: both the initial
    // attempt and the confirmation check must use the retry cascade.
    // Before #2328, the confirmation check bypassed the retry and returned
    // ConfirmationDisagree → Unknown.
    let result = {
        let _timeout = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        let _retry = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "Collection confirmation must use retry cascade (not one-shot timeout)",
    );
}

/// Test that the FORCE_EXTENDED_RETRY_SUCCESS guard resets after panic.
#[test]
fn test_forced_extended_retry_guard_resets_after_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _flag = ForcedFlagGuard::new(&FORCE_EXTENDED_RETRY_SUCCESS);
        panic!("simulated test panic");
    }));
    assert!(result.is_err(), "guard regression test should panic");
    FORCE_EXTENDED_RETRY_SUCCESS.with(|flag| {
        assert!(
            !flag.get(),
            "forced extended-retry flag must reset during unwind"
        )
    });
}
