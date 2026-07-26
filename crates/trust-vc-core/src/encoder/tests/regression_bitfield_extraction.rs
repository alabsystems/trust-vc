// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mask_low_byte() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0x1234"));
    ctx.push_obligation(ProofObligation::assert("mask", "x & 255 == 0x34"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0x1234 masked to the low byte should be 0x34");
}

#[test]
fn mask_low_nibble() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0xABCD"));
    ctx.push_obligation(ProofObligation::assert("mask", "x & 15 == 0xD"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xABCD masked to the low nibble should be 0xD");
}

#[test]
fn clear_low_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("clear", "x & 4294967294 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "masking with 4294967294 should clear the low bit of 7",
    );
}

#[test]
fn set_bit_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 4"));
    ctx.push_obligation(ProofObligation::assert("set", "x | 1 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OR with 1 should set bit zero for 4");
}

#[test]
fn toggle_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("toggle", "x ^ 1 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR with 1 should toggle bit zero for 5");
}

#[test]
fn shift_left_double() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assert("shift", "x << 1 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "left shifting 3 by one should double it to 6");
}

#[test]
fn shift_right_halve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("shift", "x >> 1 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "right shifting 10 by one should yield 5");
}

#[test]
fn extract_second_byte() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0x1234"));
    ctx.push_obligation(ProofObligation::assert("extract", "(x >> 8) & 255 == 0x12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "shifting 0x1234 right by eight and masking should extract 0x12",
    );
}

#[test]
fn power_of_two_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 8"));
    ctx.push_obligation(ProofObligation::assert("pow2", "x & (x - 1) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "8 should satisfy the power-of-two mask check");
}

#[test]
fn combine_nibbles() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hi", u32_ty());
    ctx.declare_var_typed("lo", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 0xA"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0x5"));
    ctx.push_obligation(ProofObligation::assert("combine", "(hi << 4) | lo == 0xA5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "combining 0xA and 0x5 as nibbles should yield 0xA5",
    );
}
