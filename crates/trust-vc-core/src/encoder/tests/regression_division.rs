// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn div_exact() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 20"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assert("exact", "a / b == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "20 / 4 should equal 5");
}

#[test]
fn div_truncates_toward_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assert("truncates", "a / b == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 / 2 should truncate toward zero to 3");
}

#[test]
fn div_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert("identity", "a / 1 == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "division by one should preserve the dividend");
}

#[test]
fn div_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 13"));
    ctx.push_obligation(ProofObligation::assert("self", "a / a == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nonzero value divided by itself should equal one");
}

#[test]
fn div_larger() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assert("smaller", "a / b == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 / 10 should truncate to 0");
}

#[test]
fn div_negative_dividend() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assert("signed", "a / b == -3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-7 / 2 should truncate toward zero to -3");
}

#[test]
fn div_negative_divisor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -2"));
    ctx.push_obligation(ProofObligation::assert("signed", "a / b == -3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 / -2 should truncate toward zero to -3");
}

#[test]
fn div_both_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -2"));
    ctx.push_obligation(ProofObligation::assert("signed", "a / b == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-7 / -2 should truncate toward zero to 3");
}

#[test]
fn div_mod_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "identity",
        "(a / b) * b + (a % b) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "division and remainder should reconstruct the dividend",
    );
}

#[test]
fn div_bounded_result() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_nonnegative", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "a / b >= 0 && a / b <= 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dividing [0, 100] by 10 should stay within [0, 10]",
    );
}
