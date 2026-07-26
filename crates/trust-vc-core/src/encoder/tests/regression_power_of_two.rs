// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn one_is_two_to_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("pow2", "x == (1 << 0)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 should equal 2^0 for u32");
}

#[test]
fn two_is_shift_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2"));
    ctx.push_obligation(ProofObligation::assert("pow2", "x == (1 << 1)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 should equal 1 << 1 for u32");
}

#[test]
fn four_is_shift_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 4"));
    ctx.push_obligation(ProofObligation::assert("pow2", "x == (1 << 2)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4 should equal 1 << 2 for u32");
}

#[test]
fn pow2_8_is_256() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("pow2", "(1 << 8) == 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 8 should equal 256 for u32");
}

#[test]
fn pow2_16_is_65536() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("pow2", "(1 << 16) == 65536"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 16 should equal 65536 for u32");
}

#[test]
fn pow2_and_mask() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assert("masked", "(x & 16) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 should not have bit 4 set");
}

#[test]
fn pow2_or_sets_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("set_bit", "(x | 8) == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR with 8 should set bit 3");
}

#[test]
fn pow2_shift_back() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "roundtrip",
        "((1 << 10) >> 10) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shifting 1 << 10 back by 10 should yield 1");
}

#[test]
fn pow2_multiply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("mul", "(x << 3) == x * 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "left shift by 3 should match multiply by 8");
}

#[test]
fn pow2_alignment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 64"));
    ctx.push_obligation(ProofObligation::assert("aligned", "(x & 63) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "64 should be aligned to 64");
}
