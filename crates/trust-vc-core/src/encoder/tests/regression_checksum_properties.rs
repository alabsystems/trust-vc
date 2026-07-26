// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn xor_checksum_simple() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "checksum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 170"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 85"));
    ctx.push_obligation(ProofObligation::assume("checksum_def", "checksum == a ^ b"));
    // 0xAA ^ 0x55 = 0xFF = 255
    ctx.push_obligation(ProofObligation::assert("is_255", "checksum == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xAA ^ 0x55 = 0xFF");
}

#[test]
fn xor_checksum_verify() {
    // XOR all data with checksum should yield zero
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "checksum", "verify"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("checksum_def", "checksum == a ^ b"));
    ctx.push_obligation(ProofObligation::assume(
        "verify_def",
        "verify == a ^ b ^ checksum",
    ));
    ctx.push_obligation(ProofObligation::assert("verifies_zero", "verify == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR checksum verifies to zero");
}

#[test]
fn additive_checksum_modular() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 150"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 200"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b + c"));
    ctx.push_obligation(ProofObligation::assert("is_450", "sum == 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 + 150 + 200 = 450");
}

#[test]
fn ones_complement_add() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum", "carry", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    // No carry for small values
    ctx.push_obligation(ProofObligation::assume("carry_def", "carry == sum >> 16"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == (sum & 65535) + carry",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "result == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ones complement add 5 + 3 = 8 (no carry)");
}

#[test]
fn fletcher_sum_pair() {
    // Fletcher-like: sum1 = (a + b) mod 255, sum2 = running sum of sum1s
    let mut ctx = VerificationContext::new();
    for v in &[
        "a",
        "b",
        "sum1_after_a",
        "sum1_after_b",
        "sum2_after_a",
        "sum2_after_b",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    // sum1 starts at 0
    ctx.push_obligation(ProofObligation::assume("s1a_def", "sum1_after_a == a"));
    ctx.push_obligation(ProofObligation::assume(
        "s1b_def",
        "sum1_after_b == sum1_after_a + b",
    ));
    // sum2 starts at 0
    ctx.push_obligation(ProofObligation::assume(
        "s2a_def",
        "sum2_after_a == sum1_after_a",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s2b_def",
        "sum2_after_b == sum2_after_a + sum1_after_b",
    ));
    ctx.push_obligation(ProofObligation::assert("s1_is_30", "sum1_after_b == 30"));
    ctx.push_obligation(ProofObligation::assert("s2_is_40", "sum2_after_b == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fletcher sums: s1=30, s2=10+30=40");
}

#[test]
fn parity_bit_even() {
    let mut ctx = VerificationContext::new();
    for v in &["data", "bit_count", "parity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // data has even number of 1-bits
    ctx.push_obligation(ProofObligation::assume("data_val", "data == 3"));
    // 3 = 0b11, two 1-bits
    ctx.push_obligation(ProofObligation::assume("bit_count_val", "bit_count == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "parity_def",
        "parity == bit_count & 1",
    ));
    ctx.push_obligation(ProofObligation::assert("even_parity", "parity == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 has 2 bits set, even parity");
}

#[test]
fn checksum_detects_single_error() {
    // If one byte changes, checksum changes
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "checksum_orig", "a_err", "checksum_err"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("cs_orig", "checksum_orig == a + b"));
    ctx.push_obligation(ProofObligation::assume("a_err_val", "a_err == 11"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_err",
        "checksum_err == a_err + b",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "different",
        "checksum_orig != checksum_err",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "single byte error changes additive checksum");
}

#[test]
fn crc_polynomial_step() {
    // Simplified CRC-like step: XOR with polynomial when MSB is set
    let mut ctx = VerificationContext::new();
    for v in &["state", "poly", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 5"));
    ctx.push_obligation(ProofObligation::assume("poly_val", "poly == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == state ^ poly",
    ));
    // 5 ^ 3 = 0b101 ^ 0b011 = 0b110 = 6
    ctx.push_obligation(ProofObligation::assert("is_6", "result == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CRC step: 5 ^ 3 = 6");
}

#[test]
fn luhn_double_digit() {
    // Luhn: double digit, if >= 10 subtract 9
    let mut ctx = VerificationContext::new();
    for v in &["digit", "doubled", "adjusted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("digit_val", "digit == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "doubled_def",
        "doubled == digit + digit",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "adjusted_def",
        "adjusted == if doubled >= 10 { doubled - 9 } else { doubled }",
    ));
    // 7*2 = 14 >= 10, so 14-9 = 5
    ctx.push_obligation(ProofObligation::assert("is_5", "adjusted == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Luhn: double 7 = 14, adjust to 5");
}

#[test]
fn internet_checksum_complement() {
    // Internet checksum: one's complement of sum
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum", "checksum", "verify_sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 200"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    // checksum = bitwise NOT of lower 16 bits
    ctx.push_obligation(ProofObligation::assume("cs_def", "checksum == sum ^ 65535"));
    // verify: sum + checksum should give all 1s in lower 16
    ctx.push_obligation(ProofObligation::assume(
        "verify_def",
        "verify_sum == sum + checksum",
    ));
    // 300 + (300 ^ 0xFFFF) = 300 + 65235 = 65535
    ctx.push_obligation(ProofObligation::assert("all_ones", "verify_sum == 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "sum + complement = 0xFFFF");
}
