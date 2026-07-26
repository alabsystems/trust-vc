// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn positive_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("positive_sign", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 5 should be positive");
}

#[test]
fn negative_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -5"));
    ctx.push_obligation(ProofObligation::assert("negative_sign", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == -5 should be negative");
}

#[test]
fn zero_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("zero_sign", "!(x > 0) && !(x < 0)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 0 should be neither positive nor negative");
}

#[test]
fn positive_abs_is_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("abs", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "abs_def",
        "abs == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert("positive_abs_is_self", "abs == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(7) should equal 7");
}

#[test]
fn negative_abs_is_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("abs", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -7"));
    ctx.push_obligation(ProofObligation::assume(
        "abs_def",
        "abs == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "negative_abs_is_negation",
        "abs == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(-7) should equal 7");
}

#[test]
fn sign_of_product_same_signs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("p", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bounds", "a >= 0 && a <= 10"));
    ctx.push_obligation(ProofObligation::assume("b_bounds", "b >= 0 && b <= 10"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("p_def", "p == a * b"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_of_product_same_signs",
        "p > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 * 4 should be positive");
}

#[test]
fn sign_of_product_different_signs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("p", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bounds", "a >= 0 && a <= 10"));
    ctx.push_obligation(ProofObligation::assume("b_bounds", "b >= -10 && b <= 0"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -4"));
    ctx.push_obligation(ProofObligation::assume("p_def", "p == a * b"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_of_product_different_signs",
        "p < 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 * -4 should be negative");
}

#[test]
fn nonneg_squared() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("sq", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bounds", "x >= -10 && x <= 10"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("nonneg_squared", "sq >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 squared should be nonnegative");
}

#[test]
fn sign_preserved_by_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bounds", "a >= 0 && a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_bounds", "b >= 0 && b <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_preserved_by_addition",
        "a + b > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 + 20 should stay positive");
}

#[test]
fn sign_flip_by_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("neg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bounds", "x >= 0 && x <= 10"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg == 0 - x"));
    ctx.push_obligation(ProofObligation::assert("sign_flip_by_negation", "neg < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 - 5 should be negative");
}
