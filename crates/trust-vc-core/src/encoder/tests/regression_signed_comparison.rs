// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn signed_negative_less_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("lt", "a < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signed -1 should be less than 1");
}

#[test]
fn signed_min_less_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -2147483648"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("lt", "a < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32::MIN should be less than i32::MAX");
}

#[test]
fn signed_zero_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signed zero should be nonnegative");
}

#[test]
fn unsigned_always_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unsigned values should be nonnegative");
}

#[test]
fn signed_neg_one_less_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -1"));
    ctx.push_obligation(ProofObligation::assert("lt_zero", "x < 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signed -1 should be less than zero");
}

#[test]
fn signed_positive_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert("chain", "a < b && b < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 < 2 < 3 should hold for signed values");
}

#[test]
fn signed_negative_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == -1"));
    ctx.push_obligation(ProofObligation::assert("chain", "a < b && b < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-3 < -2 < -1 should hold for signed values");
}

#[test]
fn signed_absolute_ordering() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("lt", "a < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negative signed value should be less than positive signed value",
    );
}

#[test]
fn unsigned_max_greater() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4294967295"));
    ctx.push_obligation(ProofObligation::assert("lt", "a < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 should be less than u32::MAX");
}

#[test]
fn signed_symmetric_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounds_and_sum",
        "a < 0 && b > 0 && a + b == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "symmetric signed bounds should straddle zero and sum to zero",
    );
}
