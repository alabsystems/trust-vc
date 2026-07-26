// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn isolate_lowest_set_bit() {
    // x & (-x) isolates lowest set bit
    let mut ctx = VerificationContext::new();
    for v in &["x", "neg_x", "isolated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 12 = 0b1100, lowest set bit at position 2 = value 4
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg_x == 0 - x"));
    ctx.push_obligation(ProofObligation::assume("iso_def", "isolated == x & neg_x"));
    ctx.push_obligation(ProofObligation::assert("is_4", "isolated == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 & (-12) = 4 (lowest set bit)");
}

#[test]
fn turn_off_lowest_set_bit() {
    // x & (x-1) turns off lowest set bit
    let mut ctx = VerificationContext::new();
    for v in &["x", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 12 = 0b1100, turn off bit 2: 0b1000 = 8
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == x & (x - 1)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "result == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 & 11 = 8 (clear lowest set bit)");
}

#[test]
fn set_lowest_clear_bit() {
    // x | (x+1) sets lowest clear bit
    let mut ctx = VerificationContext::new();
    for v in &["x", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 11 = 0b1011, lowest clear bit at position 2, set it: 0b1111 = 15
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 11"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == x | (x + 1)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "result == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "11 | 12 = 15 (set lowest clear bit)");
}

#[test]
fn sign_extension_i8_to_i32() {
    // Sign-extend 8-bit -5 (0xFB = 251 unsigned) to 32-bit
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("narrow", u32_ty());
    ctx.declare_var_typed("extended", i32_ty());
    ctx.push_obligation(ProofObligation::assume("n_val", "narrow == 251"));
    // If bit 7 is set (>= 128), sign extend by OR with 0xFFFFFF00
    ctx.push_obligation(ProofObligation::assume(
        "ext_def",
        "extended == if narrow >= 128 { narrow | 4294967040 } else { narrow }",
    ));
    // 251 | 0xFFFFFF00 = 0xFFFFFFFB = -5 in i32
    ctx.push_obligation(ProofObligation::assert("is_neg5", "extended == 0 - 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "sign-extend 0xFB (i8) = -5 (i32)");
}

#[test]
fn count_trailing_zeros_8() {
    // 8 = 0b1000, 3 trailing zeros
    let mut ctx = VerificationContext::new();
    for v in &["x", "ctz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 8"));
    // (x & -x) gives lowest set bit = 8 = 2^3
    ctx.push_obligation(ProofObligation::assume("ctz_val", "ctz == 3"));
    ctx.push_obligation(ProofObligation::assert("is_3", "ctz == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ctz(8) = 3");
}

#[test]
fn is_power_of_two_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("is_pow2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "pow2_def",
        "is_pow2 == if x > 0 && (x & (x - 1)) == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_power", "is_pow2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "16 is power of two");
}

#[test]
fn not_power_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("is_pow2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "pow2_def",
        "is_pow2 == if x > 0 && (x & (x - 1)) == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_power", "is_pow2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "6 is not power of two");
}

#[test]
fn next_power_of_two() {
    // For 5, next power of 2 is 8
    let mut ctx = VerificationContext::new();
    for v in &["x", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("result_val", "result == 8"));
    // 8 is power of 2 and 8 >= 5
    ctx.push_obligation(ProofObligation::assert("ge_x", "result >= x"));
    ctx.push_obligation(ProofObligation::assert("is_8", "result == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "next_power_of_two(5) = 8");
}

#[test]
fn swap_without_temp_xor() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "t1", "t2", "t3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("t1_def", "t1 == a ^ b"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == b ^ t1"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == t1 ^ t2"));
    // After XOR swap: t2 should be original a, t3 should be original b
    ctx.push_obligation(ProofObligation::assert("a_swapped", "t2 == 10"));
    ctx.push_obligation(ProofObligation::assert("b_swapped", "t3 == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR swap: (10, 20) → (10, 20)");
}

#[test]
fn byte_reverse_16bit() {
    // Reverse bytes of a 16-bit value: 0x1234 → 0x3412
    let mut ctx = VerificationContext::new();
    for v in &["val", "lo", "hi", "reversed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val_v", "val == 4660"));
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo == val & 255"));
    ctx.push_obligation(ProofObligation::assume("hi_def", "hi == (val >> 8) & 255"));
    ctx.push_obligation(ProofObligation::assume(
        "rev_def",
        "reversed == (lo << 8) | hi",
    ));
    // 0x1234: lo=0x34=52, hi=0x12=18; reversed = 52*256 + 18 = 13330 = 0x3412
    ctx.push_obligation(ProofObligation::assert("is_13330", "reversed == 13330"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "byte reverse 0x1234 → 0x3412");
}
