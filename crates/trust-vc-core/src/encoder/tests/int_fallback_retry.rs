//! Tests for integer-mode fallback retry on BV solver timeout.
//!
//! When overflow checking is enabled and the BV solver times out, the retry
//! path re-verifies with integer-mode encoding (all vars → MathInt). This is
//! sound because overflow checking already proved no arithmetic overflow.
//! Part of #2262.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::verification::test_hooks::FORCE_BV_TIMEOUT;

/// DISCRIMINATING: Tests all three int-mode fallback retry scenarios.
///
/// FORCE_BV_TIMEOUT is thread-local (#1972), so these scenarios are safe
/// under parallel test execution.
///
/// Scenarios:
/// 1. BV timeout + overflow checks → integer-mode retry recovers Verified
/// 2. BV timeout + NO overflow checks → extended-timeout retry recovers Verified
/// 3. BV timeout + overflow checks + false assertion → stays Unknown (retry fails)
#[test]
fn test_int_fallback_retry_scenarios() {
    // --- Scenario 1: Recovery via integer-mode retry ---
    {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u64"));
        ctx.push_obligation(ProofObligation::assume("x_bound", "x < 1000"));
        ctx.push_obligation(ProofObligation::assume("y_bound", "y < 1000"));
        ctx.push_obligation(ProofObligation::assert("sum_bound", "x + y < 2000"));

        // Baseline: BV verifies directly without forced timeout.
        let baseline = AYEncoder::verify(&ctx);
        expect_verified(
            &baseline,
            "Scenario 1 baseline: bounded sum should verify in BV",
        );

        // Forced BV timeout: retry via integer-mode should recover.
        let result = {
            let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
            AYEncoder::verify(&ctx)
        };

        expect_verified(
            &result,
            "Scenario 1: int-mode retry should recover Verified",
        );
    }

    // --- Scenario 2: No overflow checks → extended-timeout retry recovers ---
    // Since #2313, BV timeout without overflow checks now triggers extended-
    // timeout retry (2x timeout). Simple assertions recover via this path.
    {
        let mut ctx = VerificationContext::new(); // No .with_overflow_checks()
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
            "Scenario 2: extended-timeout retry should recover Verified",
        );
    }

    // --- Scenario 3: False assertion → retry finds counterexample ---
    // The BV solver times out (forced), but the int-mode retry finds
    // the counterexample (x==100 disproves x<50). Previously, the retry
    // discarded counterexamples and returned the original timeout Unknown.
    // Now we correctly surface the definitive answer from the retry.
    {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
        ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
        ctx.push_obligation(ProofObligation::assert("wrong", "x < 50"));

        let result = {
            let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
            AYEncoder::verify(&ctx)
        };

        expect_counterexample(
            &result,
            "Scenario 3: int-mode retry should find counterexample for false assertion",
        );
    }
}

/// Slice 2 of #2324: When int-mode retry recovers a Verified result for a
/// collection assertion, the confirmation check must also use int mode.
/// Previously, the confirmation check always used the original BV mode,
/// which would time out again → ConfirmationDisagree → false Unknown.
///
/// This test forces a BV timeout on a collection (Seq) assertion with
/// overflow checks enabled, so the int-mode retry fires. The fix ensures
/// the confirmation check also runs in int mode, producing Verified.
#[test]
fn test_int_retry_mode_propagates_to_confirmation_check() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("len_check", "s.len() >= 1"));

    // Baseline: verifies without forced timeout.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(
        &baseline,
        "Baseline: s.len()==3 => s.len()>=1 should verify",
    );

    // Forced BV timeout: int-mode retry should recover, and the
    // confirmation check should use int mode too (not BV mode that
    // would time out again). Before #2324, this returned Unknown.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    expect_verified(&result, "Int-mode retry on collection assertion should verify (confirmation check must use effective int mode)");
}

#[test]
fn test_forced_bv_timeout_guard_resets_after_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _flag = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        panic!("simulated test panic");
    }));
    assert!(result.is_err(), "guard regression test should panic");
    FORCE_BV_TIMEOUT.with(|flag| {
        assert!(
            !flag.get(),
            "forced BV-timeout flag must reset during unwind"
        )
    });
}
