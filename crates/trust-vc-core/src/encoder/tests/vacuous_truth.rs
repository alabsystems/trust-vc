//! Vacuous truth detection — catches contradictory assumptions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! When assumptions are contradictory (unsatisfiable), every assertion is
//! trivially true (solver returns Unsat for any negated assertion). This
//! is a silent false positive that wastes debugging time during competition.
//! The vacuous truth check in verify_typed detects this and returns Unknown.
//!
//! Part of #2187.

use super::*;

/// Contradictory assumptions: x > 10 AND x < 5 — impossible.
/// Should return Unknown (vacuous truth detected), NOT Verified.
#[test]
fn test_contradictory_assumes_detected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_big", "x > 10"));
    ctx.push_obligation(ProofObligation::assume("x_small", "x < 5"));
    ctx.push_obligation(ProofObligation::assert("anything", "x == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Contradictory assumptions should be detected as vacuous truth",
    );
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            reason.contains("contradictory") || reason.contains("vacuous"),
            "Unknown reason should mention contradictory/vacuous, got: {}",
            reason
        );
    }
}

/// Contradictory requires: requires(x == 5) AND requires(x == 10).
/// The requires are treated as assumptions in BodyLevel verification mode.
#[test]
fn test_contradictory_requires_detected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.obligations
        .push(ProofObligation::requires("req_five", "x == 5"));
    ctx.obligations
        .push(ProofObligation::requires("req_ten", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("trivial_true", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Contradictory requires should be detected as vacuous truth",
    );
}

/// Contradictory assumptions that are only contradictory under int-mode.
///
/// For `u8`, `x == 255 && x + 1 == 0` is satisfiable in BV mode due to wrap,
/// but contradictory in int-mode where arithmetic is mathematical. Measure
/// obligations verify in int-mode, so the vacuous precheck must rerun there.
#[test]
fn test_int_mode_only_contradiction_is_detected_as_vacuous() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("max_u8", "x == 255"));
    ctx.push_obligation(ProofObligation::assume("wrapped_zero", "x + 1 == 0"));
    ctx.obligations
        .push(ProofObligation::measure_non_negative("nonneg", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "int-mode-only contradictions must be caught by the vacuous precheck",
    );
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            reason.contains("contradictory") || reason.contains("vacuous"),
            "int-mode vacuity should report the standard contradictory-context message, got: {reason}",
        );
    }
}

/// Non-contradictory assumptions with a true assertion: should Verify normally.
/// Control test — ensures the vacuous check doesn't false-positive.
#[test]
fn test_consistent_assumes_verify_normally() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 100"));
    ctx.push_obligation(ProofObligation::assert("in_range", "x > 0 && x < 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Consistent assumptions with true assertion should verify",
    );
}

/// Non-contradictory assumptions with a false assertion: should Counterexample.
/// Control test — ensures the vacuous check doesn't interfere with normal
/// Counterexample production.
#[test]
fn test_consistent_assumes_false_assertion_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 100"));
    ctx.push_obligation(ProofObligation::assert("impossible", "x > 200"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Consistent assumptions with false assertion should counterexample",
    );
}

/// Without the vacuous truth check, this would incorrectly return Verified:
/// the assertion `false` is trivially true under contradictory assumptions.
/// This is the key soundness test — `false` should NEVER verify.
#[test]
fn test_assert_false_under_contradiction_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("contradiction_a", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("contradiction_b", "x == 2"));
    ctx.push_obligation(ProofObligation::assert("literal_false", "false"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "assert!(false) under contradictory assumptions must NOT verify",
    );
}
