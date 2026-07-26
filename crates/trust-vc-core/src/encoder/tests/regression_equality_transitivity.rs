// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn eq_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assert("eq_reflexive", "a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equality should be reflexive");
}

#[test]
fn eq_symmetric() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a == b"));
    ctx.push_obligation(ProofObligation::assert("ba", "b == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equality should be symmetric");
}

#[test]
fn eq_transitive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("chain", "a == b && b == c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a == c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equality should be transitive");
}

#[test]
fn eq_chain_four() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("d", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "chain",
        "a == b && b == c && c == d",
    ));
    ctx.push_obligation(ProofObligation::assert("ad", "a == d"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "four-step equality chain should hold");
}

#[test]
fn eq_substitution_add() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a == b"));
    ctx.push_obligation(ProofObligation::assert("add_subst", "a + c == b + c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equal values should remain equal under addition");
}

#[test]
fn eq_substitution_mul() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "values",
        "a == 5 && b == 5 && c == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mul_subst", "a * c == b * c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "equal concrete values should remain equal under multiplication",
    );
}

#[test]
fn neq_irreflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assert("eq_self", "a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a value should equal itself");
}

#[test]
fn eq_concrete_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "values",
        "x == 10 && y == 10 && z == 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "chain",
        "x == y && y == z && x == z",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equal concrete chain should verify");
}

#[test]
fn eq_derived_property() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("premises", "a == b && a > 0"));
    ctx.push_obligation(ProofObligation::assert("b_pos", "b > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "positive property should transfer across equality");
}

#[test]
fn eq_double_substitution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("chain", "a == b && b == c"));
    ctx.push_obligation(ProofObligation::assert("shifted", "a + 1 == c + 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "equality chain should support repeated substitution",
    );
}
