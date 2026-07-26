// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn add_zero_identity_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("add_zero", "x + 0 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 addition by zero should preserve 42");
}

#[test]
fn add_zero_identity_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("add_zero", "x + 0 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 addition by zero should preserve 42");
}

#[test]
fn mul_one_identity_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("mul_one", "x * 1 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 multiplication by one should preserve 42");
}

#[test]
fn mul_one_identity_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("mul_one", "x * 1 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 multiplication by one should preserve 42");
}

#[test]
fn mul_zero_annihilator() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("mul_zero", "x * 0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 multiplication by zero should yield zero");
}

#[test]
fn xor_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("xor_zero", "(x ^ 0) == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "xor with zero should preserve 42");
}

#[test]
fn and_max_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("and_max", "(x & 4294967295) == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "and with all ones should preserve 42");
}

#[test]
fn or_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("or_zero", "(x | 0) == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "or with zero should preserve 42");
}

#[test]
fn sub_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("sub_zero", "x - 0 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "subtraction by zero should preserve 42");
}

#[test]
fn div_one_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("div_one", "x / 1 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "division by one should preserve 42");
}
