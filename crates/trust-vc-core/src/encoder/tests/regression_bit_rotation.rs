// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn shift_left_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 1) == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 << 1 = 10");
}

#[test]
fn shift_right_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 1) == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "10 >> 1 = 5");
}

#[test]
fn shift_left_then_right() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("shifted", u32_ty());
    ctx.declare_var_typed("back", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume("shifted_def", "shifted == x << 2"));
    ctx.push_obligation(ProofObligation::assume("back_def", "back == shifted >> 2"));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "back == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7 << 2 >> 2 = 7 (no overflow)");
}

#[test]
fn double_via_shift() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 13"));
    ctx.push_obligation(ProofObligation::assert("doubled", "(x << 1) == 26"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "13 << 1 = 26");
}

#[test]
fn shift_preserves_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("still_zero", "(x << 5) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0 << 5 = 0");
}

#[test]
fn mask_low_byte() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 4660"));
    ctx.push_obligation(ProofObligation::assert("low_byte", "(x & 255) == 52"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0x1234 & 0xFF = 0x34 (52)");
}

#[test]
fn extract_second_byte() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("shifted", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 43981"));
    ctx.push_obligation(ProofObligation::assume("shifted_def", "shifted == x >> 8"));
    ctx.push_obligation(ProofObligation::assert(
        "second_byte",
        "(shifted & 255) == 171",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xABCD >> 8 & 0xFF = 0xAB (171)");
}

#[test]
fn set_bit_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("bit_set", "(x | 8) == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0 | 8 = 8 (set bit 3)");
}

#[test]
fn clear_low_bit_via_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assert("cleared", "(x & 14) == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "15 & 14 = 14 (clear bit 0)");
}

#[test]
fn xor_toggle_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("mask", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 170"));
    ctx.push_obligation(ProofObligation::assume("mask_val", "mask == 255"));
    ctx.push_obligation(ProofObligation::assert("toggled", "(x ^ mask) == 85"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xAA ^ 0xFF = 0x55 (85)");
}
