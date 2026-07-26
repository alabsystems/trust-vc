// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn u8_max_plus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("wraps", "x + 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 max plus one should wrap to zero");
}

#[test]
fn u8_zero_minus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("wraps", "x - 1 == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 zero minus one should wrap to 255");
}

#[test]
fn i32_negation_of_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("negates", "0 - x == -1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "subtracting one from zero should yield minus one");
}

#[test]
fn i32_min_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("negative", "x < 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 minimum value should be negative");
}

#[test]
fn i32_max_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 maximum value should be positive");
}

#[test]
fn u32_max_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 4294967295"));
    ctx.push_obligation(ProofObligation::assert("wraps", "x + 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 maximum value plus one should wrap to zero");
}

#[test]
fn xor_with_all_ones_is_not() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 170"));
    ctx.push_obligation(ProofObligation::assert("xor_not", "(x ^ 255) == 85"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "xor with all ones should flip every bit");
}

#[test]
fn and_with_zero_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12345"));
    ctx.push_obligation(ProofObligation::assert("and_zero", "(x & 0) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "and with zero should yield zero");
}

#[test]
fn or_with_zero_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12345"));
    ctx.push_obligation(ProofObligation::assert("or_zero", "(x | 0) == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "or with zero should preserve the value");
}

#[test]
fn shift_left_one_doubles() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("shift", "(x << 1) == 84"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "left shifting by one should double 42");
}
