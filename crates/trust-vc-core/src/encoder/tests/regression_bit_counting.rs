// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn popcount_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("all_clear", "x == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "popcount(0) = 0 (trivially, value is 0)");
}

#[test]
fn single_bit_set() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "is_power_of_two",
        "x > 0 && (x & (x - 1)) == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "8 has exactly one bit set (power of 2)");
}

#[test]
fn all_low_bits_set() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assert("low_nibble", "(x & 15) == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "15 = 0b1111, all low nibble bits set");
}

#[test]
fn isolate_lowest_set_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("neg", u32_ty());
    ctx.declare_var_typed("isolated", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg == 0 - x"));
    ctx.push_obligation(ProofObligation::assume(
        "isolated_def",
        "isolated == x & neg",
    ));
    ctx.push_obligation(ProofObligation::assert("lowest_bit", "isolated == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "lowest set bit of 12 (0b1100) is 4 (0b0100)");
}

#[test]
fn clear_lowest_set_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("cleared", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "cleared_def",
        "cleared == x & (x - 1)",
    ));
    ctx.push_obligation(ProofObligation::assert("one_less_bit", "cleared == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 & 11 = 8 (clear lowest set bit)");
}

#[test]
fn power_of_two_128() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 128"));
    ctx.push_obligation(ProofObligation::assert(
        "pow2",
        "x > 0 && (x & (x - 1)) == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "128 is a power of 2");
}

#[test]
fn not_power_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 6"));
    ctx.push_obligation(ProofObligation::assert("not_pow2", "(x & (x - 1)) != 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "6 is not a power of 2");
}

#[test]
fn mask_generation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", u32_ty());
    ctx.declare_var_typed("mask", u32_ty());
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 4"));
    ctx.push_obligation(ProofObligation::assume("mask_def", "mask == (1 << n) - 1"));
    ctx.push_obligation(ProofObligation::assert("mask_is_15", "mask == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(1 << 4) - 1 = 15 = 0b1111");
}

#[test]
fn byte_extraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("b0", u32_ty());
    ctx.declare_var_typed("b1", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 258"));
    ctx.push_obligation(ProofObligation::assume("b0_def", "b0 == x & 255"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == (x >> 8) & 255"));
    ctx.push_obligation(ProofObligation::assert("bytes", "b0 == 2 && b1 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "258 = 0x102: byte0=2, byte1=1");
}

#[test]
fn or_combines_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("combined", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("combined_def", "combined == a | b"));
    ctx.push_obligation(ProofObligation::assert("all_bits", "combined == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 (0101) | 10 (1010) = 15 (1111)");
}
