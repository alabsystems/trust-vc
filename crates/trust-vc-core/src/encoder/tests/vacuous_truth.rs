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

/// The vacuous precheck must RERUN in int-mode: a measure obligation is the
/// only obligation here, and it is discharged in the `Int` universe, so nothing
/// else would ever look at this hypothesis set.
///
/// The contradiction is drawn from `requires` clauses, which are SPEC code and
/// therefore read as mathematical integers on both sides of a call
/// (`crate::spec_arith`): for a `u8`, `x == 255` and `x + 1 == 0` cannot both
/// hold of the integers, and that is true of the ONE reading both facts carry.
#[test]
fn test_int_mode_vacuity_fires_on_a_contradiction_real_in_that_reading() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.obligations
        .push(ProofObligation::requires("max_u8", "x == 255"));
    ctx.obligations
        .push(ProofObligation::requires("successor_zero", "x + 1 == 0"));
    ctx.obligations
        .push(ProofObligation::measure_non_negative("nonneg", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "int-mode contradictions must be caught by the vacuous precheck",
    );
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            reason.contains("contradictory") || reason.contains("vacuous"),
            "int-mode vacuity should report the standard contradictory-context message, got: {reason}",
        );
    }
}

/// LIAR TWIN, and a correction of record. This test previously asserted that
/// the SAME two facts written as fixed-width `assume!`s were "contradictory in
/// int-mode", and it passed because the int lane re-read a bit-vector fact over
/// the unbounded integers. That re-reading is the cross-lane false-verify this
/// tree closed (`encoder::verification::arith_reading`): `x + 1 == 0` was
/// ESTABLISHED under the wrapping reading, where `x == 255` satisfies it, and
/// the int lane may not re-read it.
///
/// So the hypotheses are consistent, and `Verified` is the right answer — not a
/// vacuous one: `x >= 0` is true of every `u8`, in either reading, with or
/// without the hypotheses. The pin is that the precheck does not invent a
/// contradiction out of a change of reading.
#[test]
fn test_a_fixed_width_assumption_is_not_re_read_as_an_int_contradiction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("max_u8", "x == 255"));
    ctx.push_obligation(ProofObligation::assume("wrapped_zero", "x + 1 == 0"));
    ctx.obligations
        .push(ProofObligation::measure_non_negative("nonneg", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a wrapping-established `assume!` must not read as an int contradiction",
    );
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
