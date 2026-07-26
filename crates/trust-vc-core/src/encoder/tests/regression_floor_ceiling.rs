// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn div_exact() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("exact", "x / 2 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 / 2 should equal 5 for u32");
}

#[test]
fn div_truncates_down() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("truncates", "x / 2 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 / 2 should truncate down to 3 for u32");
}

#[test]
fn div_by_itself() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("self", "x / 42 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42 / 42 should equal 1 for u32");
}

#[test]
fn div_smaller_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assert("smaller", "x / 10 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 / 10 should truncate to 0 for u32");
}

#[test]
fn mod_complement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("remainder", "x % 3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 % 3 should equal 1 for u32");
}

#[test]
fn div_mod_reconstruct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("d", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "reconstruct",
        "(x / d) * d + (x % d) == x",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "division and remainder should reconstruct 17");
}

#[test]
fn div_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assert("monotone", "a / 3 <= b / 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "division by the same positive divisor should preserve order",
    );
}

#[test]
fn mod_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("d", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 7"));
    ctx.push_obligation(ProofObligation::assert("bounded", "x % d < d"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 remainder should stay below a positive divisor",
    );
}

#[test]
fn signed_div_truncates_toward_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -7"));
    ctx.push_obligation(ProofObligation::assert("truncates", "x / 2 == -3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signed BV division should truncate toward zero, not floor",
    );
}

#[test]
fn signed_mod_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -7"));
    ctx.push_obligation(ProofObligation::assert("sign", "x % 3 == -1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signed BV remainder should keep the dividend sign");
}
