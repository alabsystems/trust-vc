// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn u8_small_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 50"));
    ctx.push_obligation(ProofObligation::assert("sum_150", "a + b == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 + 50 = 150 fits in u8");
}

#[test]
fn u8_wrapping_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assert("wrap_44", "a + b == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200 + 100 = 300 wraps to 44 mod 256 in u8");
}

#[test]
fn u32_large_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1000000"));
    ctx.push_obligation(ProofObligation::assert("x_big", "x > 999999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1000000 > 999999");
}

#[test]
fn u32_subtraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 50"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 30"));
    ctx.push_obligation(ProofObligation::assert("diff_20", "a - b == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "50 - 30 = 20 for u32");
}

#[test]
fn u64_wide_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1000000000"));
    ctx.push_obligation(ProofObligation::assert("x_big", "x > 999999999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 billion > 999999999 in u64");
}

#[test]
fn u64_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 500"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 300"));
    ctx.push_obligation(ProofObligation::assert("sum_800", "a + b == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "500 + 300 = 800 in u64");
}

#[test]
fn i32_negative_values() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "y_bound",
        "y >= -1000 && y <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == -3"));
    ctx.push_obligation(ProofObligation::assert("sum_neg8", "x + y == -8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-5 + -3 = -8 with bounds");
}

#[test]
fn i32_mixed_sign_subtraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a_bound",
        "a >= -1000 && a <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bound",
        "b >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -7"));
    ctx.push_obligation(ProofObligation::assert("diff_17", "a - b == 17"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 - (-7) = 17 with bounds");
}

#[test]
fn u32_modular_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("mod_7", "x % 7 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 % 7 = 2");
}

#[test]
fn i32_absolute_via_conditional() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -5"));
    ctx.push_obligation(ProofObligation::assert(
        "abs_5",
        "if x >= 0 { x } else { 0 - x } == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(-5) = 5 via if-then-else");
}
