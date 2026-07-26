// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn real_addition_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("commut", "a + b == b + a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real addition is commutative");
}

#[test]
fn real_multiplication_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("commut", "a * b == b * a"));
    let result = AYEncoder::verify(&ctx);
    // Hint-free nonlinear REAL arithmetic is deliberately outside the default
    // prover profile (the Verus `smt.arith.nl=false` analog), so this TRUE fact
    // is not proved without `by(nonlinear_arith)`. Under
    // `docs/design-unknown-as-failure.md` that incompleteness is reported as a
    // model-less FAILURE, not a soft Unknown — the conservative reading, and
    // the one that matches upstream.
    expect_incompleteness_modelless_failure(&result, "real multiplication is commutative");
}

#[test]
fn real_additive_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("identity", "a + 0 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real additive identity holds");
}

#[test]
fn real_multiplicative_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("identity", "a * 1 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real multiplicative identity holds");
}

#[test]
fn real_distributive_law() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("c", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert(
        "distrib",
        "a * (b + c) == a * b + a * c",
    ));
    let result = AYEncoder::verify(&ctx);
    // Hint-free nonlinear REAL arithmetic: see `real_multiplication_commutative`.
    expect_incompleteness_modelless_failure(&result, "real distributive law holds");
}

#[test]
fn real_subtraction_self_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("self_zero", "a - a == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real subtraction by self yields zero");
}

#[test]
fn real_double_equals_two_times_x() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert("double", "a + a == 2 * a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real doubling matches multiplication by two");
}

#[test]
fn real_nonzero_product() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("a_nz", "a != 0"));
    ctx.push_obligation(ProofObligation::assume("b_nz", "b != 0"));
    ctx.push_obligation(ProofObligation::assert("nonzero_product", "a * b != 0"));
    let result = AYEncoder::verify(&ctx);
    // Hint-free nonlinear REAL arithmetic: see `real_multiplication_commutative`.
    expect_incompleteness_modelless_failure(&result, "nonzero real factors imply nonzero product");
}

#[test]
fn real_division_by_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("a_nz", "a != 0"));
    ctx.push_obligation(ProofObligation::assert("div_self", "a / a == 1"));
    let result = AYEncoder::verify(&ctx);
    // Division by a SYMBOLIC (non-constant) real divisor is nonlinear real
    // arithmetic, which the DEFAULT prover profile refuses as theory
    // incompleteness (the Verus-faithful `smt.arith.nl=false` analog — in
    // Verus, `x/x == 1` is the canonical fact that REQUIRES
    // `by(nonlinear_arith)`). trust-vc used to prove this hint-free via its
    // self-cancellation axiom — a sound but Verus-DIVERGING superset; the
    // default boundary now surfaces the same model-less incompleteness
    // failure Verus's default query does. The fact stays true and provable in
    // principle under the nonlinear hint path (pre-pass division-rule
    // completeness for `/`-cancellation is a capability follow-up).
    expect_incompleteness_modelless_failure(
        &result,
        "a / a == 1 (hint-free symbolic-divisor division on the default prover profile)",
    );
}

/// ADVERSARIAL (no false Verified): self-cancellation gives `a / a == 1`, never
/// `a / a == 2`. The wrong constant must not verify. (It surfaces as
/// Unknown rather than a concrete counterexample because the bare SMT `/` is
/// opaque on a symbolic divisor, so no model is fabricated — fail-closed.)
#[test]
fn real_division_by_self_wrong_constant_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("a_nz", "a != 0"));
    ctx.push_obligation(ProofObligation::assert("div_self_two", "a / a == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "a / a == 2 is false; must not verify");
}

/// ADVERSARIAL (no false Verified): the self-cancellation axiom fires ONLY when
/// numerator and divisor are the same term. For distinct `a` and `b` (with
/// `b != 0`, `a != b`), `a / b == 1` is false and must not verify.
#[test]
fn real_division_distinct_operands_not_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("b_nz", "b != 0"));
    ctx.push_obligation(ProofObligation::assume("a_ne_b", "a != b"));
    ctx.push_obligation(ProofObligation::assert("div_distinct_one", "a / b == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "a / b == 1 with a != b must not verify");
}

#[test]
fn real_addition_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("c", crate::ir::TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assert(
        "assoc",
        "(a + b) + c == a + (b + c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real addition is associative");
}
