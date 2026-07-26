//! Path A arithmetic normalization integration tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for TrustVcExpr-level equality substitution + arithmetic
//! normalization in the Path A (`VerificationContext`) encoding pipeline.
//! These are the target equalities from the GCD lemma chain described in
//! `designs/2026-03-18-2386-verifythis-path-a-residuals.md` Slice C.
//!
//! Part of #2187 (VerifyThis Path A arithmetic normalization).

use super::*;

/// GCD target equality 1: `q * y == d * (q * q2)` given `y == d * q2`.
///
/// After substitution: `q * (d * q2) == d * (q * q2)`.
/// After normalization: both sides canonicalize to `((d * q) * q2)`.
#[test]
fn test_gcd_q_mul_y_eq_d_mul_q_mul_q2() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q2", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("int"));

    // Assumption: y == d * q2
    ctx.push_obligation(ProofObligation::assume("y_def", "y == d * q2"));

    // Assertion: q * y == d * (q * q2)
    ctx.push_obligation(ProofObligation::assert("step1", "q * y == d * (q * q2)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "q * y == d * (q * q2) with y == d * q2 should verify via substitution + normalization",
    );
}

/// GCD target equality 2: `x == d * (q * q2) + r` given `x == q * y + r`
/// and `y == d * q2`.
///
/// After substituting y: `x == q * (d * q2) + r`.
/// After normalizing: both sides of the chain equate through congruence.
#[test]
fn test_gcd_x_eq_d_mul_q_mul_q2_plus_r() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q2", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("r", crate::ir::TrustVcType::parse_or_opaque("int"));

    ctx.push_obligation(ProofObligation::assume("y_def", "y == d * q2"));
    ctx.push_obligation(ProofObligation::assume("x_def", "x == q * y + r"));

    // After substituting y into x_def: x == q * (d * q2) + r
    // The assertion states the same thing: x == d * (q * q2) + r
    // After normalization both mul sides become ((d * q) * q2) + r
    ctx.push_obligation(ProofObligation::assert("step2", "x == d * (q * q2) + r"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x == d * (q * q2) + r with x == q * y + r and y == d * q2 should verify",
    );
}

/// Normalization without substitution: structurally identical after
/// reordering commutative operands.
#[test]
fn test_mul_commutativity_verifies_directly() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("int"));

    // a * (b * c) == b * (a * c) — both normalize to ((a * b) * c)
    ctx.push_obligation(ProofObligation::assert(
        "comm",
        "a * (b * c) == b * (a * c)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a * (b * c) == b * (a * c) should verify via normalization",
    );
}

/// GCD target equality 3: `x == d * (q * q2 + q3)` given `x == d * q1`
/// and `q1 == q * q2 + q3`.
///
/// After back-propagation in add_typed_assumption: x's binding updates
/// from `d * q1` to `d * (q * q2 + q3)`. Assertion substitutes x →
/// `d * (q * q2 + q3)`, making both sides identical. Part of #2400.
#[test]
fn test_gcd_x_eq_d_mul_sum_via_back_propagation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q1", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q2", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q3", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));

    // Assumption order matters for back-propagation:
    // x == d * q1 comes first, then q1 == q * q2 + q3 triggers
    // back-propagation into x's binding.
    ctx.push_obligation(ProofObligation::assume("x_def", "x == d * q1"));
    ctx.push_obligation(ProofObligation::assume("q1_def", "q1 == q * q2 + q3"));

    ctx.push_obligation(ProofObligation::assert("target3", "x == d * (q * q2 + q3)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == d*(q*q2+q3) with x==d*q1 and q1==q*q2+q3 should verify via back-propagation + substitution");
}

/// GCD target equality 4: `r == d * q3` from the full GCD assumption chain.
///
/// Assumptions: y==d*q2, x==q*y+r, q1==q*q2+q3, x==d*q1.
/// The fourth assumption, after substitution + distribution, becomes
/// `(d*q)*q2 + r == (d*q)*q2 + d*q3`, from which ay's Int theory
/// derives `r == d*q3`. Part of #2400.
#[test]
fn test_gcd_r_eq_d_mul_q3_full_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q1", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q2", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q3", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("r", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("int"));

    ctx.push_obligation(ProofObligation::assume("y_def", "y == d * q2"));
    ctx.push_obligation(ProofObligation::assume("x_div", "x == q * y + r"));
    ctx.push_obligation(ProofObligation::assume("q1_def", "q1 == q * q2 + q3"));
    ctx.push_obligation(ProofObligation::assume("x_d", "x == d * q1"));

    ctx.push_obligation(ProofObligation::assert("target4", "r == d * q3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "r == d*q3 from full GCD chain should verify via substitution + distribution + Int theory",
    );
}

/// Reverse-order GCD chain: same logical problem as `test_gcd_r_eq_d_mul_q3_full_chain`
/// but with the assumption order used by the practice benchmark (x_d first).
///
/// Without reconciliation, the single-pass encoder misses late bindings:
/// x_d encoded before q1_def means ay sees `d*q1 == d*q*q2 + r` with
/// symbolic q1. Reconciliation re-encodes with the final binding map,
/// producing the derived equality `d*q3 == r`. Part of #2386.
#[test]
fn test_gcd_r_eq_d_mul_q3_reverse_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q1", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q2", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("q3", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("r", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("int"));

    // Practice benchmark order: x_d first (before q1 is decomposed).
    ctx.push_obligation(ProofObligation::assume("x_d", "x == d * q1"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == d * q2"));
    ctx.push_obligation(ProofObligation::assume("x_div", "x == q * y + r"));
    ctx.push_obligation(ProofObligation::assume("q1_def", "q1 == q * q2 + q3"));

    ctx.push_obligation(ProofObligation::assert("target4", "r == d * q3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "r == d*q3 from reverse-order GCD chain should verify via equality reconciliation",
    );
}

/// Duplicate binding derivation: two equality assumptions for the same
/// variable produce a cross-derived equality. Tests the explicit derivation
/// path in `add_typed_assumption` when `entry().or_insert()` detects a
/// duplicate. Both orderings should verify identically. Part of #2406.
#[test]
fn test_duplicate_binding_derives_cross_equality() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));

    // Two assumptions bind x to different expressions.
    // Derived cross-equality: a + b == c, which proves the goal.
    ctx.push_obligation(ProofObligation::assume("x_ab", "x == a + b"));
    ctx.push_obligation(ProofObligation::assume("x_c", "x == c"));

    ctx.push_obligation(ProofObligation::assert("goal", "a + b == c"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a+b == c from duplicate x binding should verify");
}

/// Same as above but with reversed assumption order — exercises the
/// path where the second binding is the complex expression. Part of #2406.
#[test]
fn test_duplicate_binding_reversed_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("int"));

    ctx.push_obligation(ProofObligation::assume("x_c", "x == c"));
    ctx.push_obligation(ProofObligation::assume("x_ab", "x == a + b"));

    ctx.push_obligation(ProofObligation::assert("goal", "a + b == c"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a+b == c from reversed duplicate x binding should verify",
    );
}

/// Addition commutativity + associativity through normalization.
#[test]
fn test_add_commutativity_verifies_directly() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("int"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("int"));

    // (c + a) + b == (a + b) + c — both normalize to ((a + b) + c)
    ctx.push_obligation(ProofObligation::assert(
        "comm_add",
        "(c + a) + b == (a + b) + c",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(c + a) + b == (a + b) + c should verify via normalization",
    );
}
