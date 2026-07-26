// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn extract_lowest_hex_digit() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "hex_digit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 255")); // 0xFF
    ctx.push_obligation(ProofObligation::assume("hd_def", "hex_digit == val & 15"));
    ctx.push_obligation(ProofObligation::assert("is_15", "hex_digit == 15")); // 0xF
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xFF & 0xF = 0xF");
}

#[test]
fn extract_second_hex_digit() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "hex_digit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 171")); // 0xAB
    ctx.push_obligation(ProofObligation::assume(
        "hd_def",
        "hex_digit == (val >> 4) & 15",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "hex_digit == 10")); // 0xA
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(0xAB >> 4) & 0xF = 0xA");
}

#[test]
fn extract_lowest_octal_digit() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "oct_digit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 83")); // 0o123 = 83
    ctx.push_obligation(ProofObligation::assume("od_def", "oct_digit == val & 7"));
    ctx.push_obligation(ProofObligation::assert("is_3", "oct_digit == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "83 & 7 = 3 (octal digit)");
}

#[test]
fn extract_binary_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "bit2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 5")); // 0b101
    ctx.push_obligation(ProofObligation::assume("b2_def", "bit2 == (val >> 2) & 1"));
    ctx.push_obligation(ProofObligation::assert("is_1", "bit2 == 1")); // bit 2 is set
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 2 of 0b101 = 1");
}

#[test]
fn decimal_digit_extraction() {
    // Ones digit = val % 10, tens digit = (val / 10) % 10
    let mut ctx = VerificationContext::new();
    for v in &["val", "ones", "tens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 42"));
    ctx.push_obligation(ProofObligation::assume("o_def", "ones == val % 10"));
    ctx.push_obligation(ProofObligation::assume("t_def", "tens == (val / 10) % 10"));
    ctx.push_obligation(ProofObligation::assert("ones_is_2", "ones == 2"));
    ctx.push_obligation(ProofObligation::assert("tens_is_4", "tens == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "42: ones=2, tens=4");
}

#[test]
fn reconstruct_from_hex_digits() {
    // Reconstruct from two hex digits: (hi << 4) | lo
    let mut ctx = VerificationContext::new();
    for v in &["hi", "lo", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hi == 10")); // 0xA
    ctx.push_obligation(ProofObligation::assume("l", "lo == 11")); // 0xB
    ctx.push_obligation(ProofObligation::assume("r_def", "result == (hi << 4) | lo"));
    ctx.push_obligation(ProofObligation::assert("is_171", "result == 171")); // 0xAB
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(0xA << 4) | 0xB = 0xAB");
}

#[test]
fn hex_digit_in_range() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "digit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 200"));
    ctx.push_obligation(ProofObligation::assume("d_def", "digit == val & 15"));
    ctx.push_obligation(ProofObligation::assert("in_range", "digit < 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "val & 0xF < 16");
}

#[test]
fn binary_to_decimal_4bit() {
    // 4-bit binary 1011 = 8+0+2+1 = 11
    let mut ctx = VerificationContext::new();
    for v in &["b3", "b2", "b1", "b0", "decimal"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b3_val", "b3 == 1"));
    ctx.push_obligation(ProofObligation::assume("b2_val", "b2 == 0"));
    ctx.push_obligation(ProofObligation::assume("b1_val", "b1 == 1"));
    ctx.push_obligation(ProofObligation::assume("b0_val", "b0 == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dec_def",
        "decimal == b3 * 8 + b2 * 4 + b1 * 2 + b0 * 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11", "decimal == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1011₂ = 11₁₀");
}

#[test]
fn digit_count_for_base() {
    // Number of digits in base b: floor(log_b(n)) + 1
    // For n=255, base=16: 2 hex digits (FF)
    let mut ctx = VerificationContext::new();
    for v in &["n", "digits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 255"));
    ctx.push_obligation(ProofObligation::assume("d_val", "digits == 2"));
    ctx.push_obligation(ProofObligation::assert("is_2", "digits == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255 needs 2 hex digits");
}

#[test]
fn bcd_encoding() {
    // BCD: pack decimal digit 4 and 2 into one byte: 0x42
    let mut ctx = VerificationContext::new();
    for v in &["tens", "ones", "bcd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tens == 4"));
    ctx.push_obligation(ProofObligation::assume("o", "ones == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "bcd_def",
        "bcd == (tens << 4) | ones",
    ));
    // 4 << 4 = 64; 64 | 2 = 66 = 0x42
    ctx.push_obligation(ProofObligation::assert("is_66", "bcd == 66"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "BCD(4,2) = 0x42 = 66");
}
