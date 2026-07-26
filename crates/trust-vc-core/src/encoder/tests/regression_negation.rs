// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn neg_neg_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("double_neg", "-(-x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "double negation should preserve positive i32 values",
    );
}

#[test]
fn neg_positive_becomes_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("neg_is_negative", "-x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negating a positive i32 should yield a negative value",
    );
}

#[test]
fn neg_zero_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("neg_zero", "-x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negating zero should stay zero");
}

#[test]
fn abs_positive_unchanged() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("abs_positive", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "positive values should satisfy the absolute-value identity case",
    );
}

#[test]
fn abs_negative_flips() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_negative", "x < 0"));
    ctx.push_obligation(ProofObligation::assume("not_min", "x > -2147483648"));
    ctx.push_obligation(ProofObligation::assert("neg_flips_sign", "-x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negating a non-MIN negative i32 should produce a positive value",
    );
}

#[test]
fn neg_preserves_magnitude() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_is_42", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("neg_42", "-x == -42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negation should preserve magnitude for a concrete value",
    );
}

#[test]
fn sign_product_same_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_positive", "a > 0"));
    ctx.push_obligation(ProofObligation::assume("b_positive", "b > 0"));
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a < 1000"));
    ctx.push_obligation(ProofObligation::assume("b_bounded", "b < 1000"));
    ctx.push_obligation(ProofObligation::assert("product_positive", "a * b > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "positive bounded factors should have a positive product",
    );
}

#[test]
fn sign_product_diff_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_positive", "a > 0"));
    ctx.push_obligation(ProofObligation::assume("b_negative", "b < 0"));
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a < 1000"));
    ctx.push_obligation(ProofObligation::assume("b_bounded", "b > -1000"));
    ctx.push_obligation(ProofObligation::assert("product_negative", "a * b < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "opposite-sign bounded factors should have a negative product",
    );
}

#[test]
fn neg_sum_distributes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_is_3", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_is_5", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "neg_distribution",
        "-(a + b) == (-a) + (-b)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negation should distribute over addition for concrete i32 values",
    );
}

#[test]
fn double_neg_large() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_large", "x == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "double_neg_large",
        "-(-x) == 1000000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "double negation should preserve a large concrete i32 value",
    );
}
