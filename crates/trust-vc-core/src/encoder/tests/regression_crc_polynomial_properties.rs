// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn xor_with_zero_is_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["data", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "data == 42"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == data ^ 0"));
    ctx.push_obligation(ProofObligation::assert("identity", "result == data"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "x ^ 0 = x");
}

#[test]
fn xor_with_self_is_zero() {
    let mut ctx = VerificationContext::new();
    for v in &["data", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "data == 42"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == data ^ data"));
    ctx.push_obligation(ProofObligation::assert("zero", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "x ^ x = 0");
}

#[test]
fn crc_remainder_bounded() {
    // CRC remainder is always < polynomial (divisor)
    let mut ctx = VerificationContext::new();
    for v in &["remainder", "polynomial"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "remainder == 7"));
    ctx.push_obligation(ProofObligation::assume("p", "polynomial == 16"));
    ctx.push_obligation(ProofObligation::assert("bounded", "remainder < polynomial"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRC remainder 7 < poly 16");
}

#[test]
fn shift_and_xor_step() {
    // CRC step: shift left, XOR with poly if MSB was set
    let mut ctx = VerificationContext::new();
    for v in &["reg", "shifted", "result", "poly"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "reg == 5")); // 0b0101
    ctx.push_obligation(ProofObligation::assume("p", "poly == 3")); // 0b0011
    ctx.push_obligation(ProofObligation::assume("sh_def", "shifted == reg << 1"));
    // No MSB set (reg < 128 for 8-bit), so no XOR
    ctx.push_obligation(ProofObligation::assume(
        "res_def",
        "result == if reg >= 128 { shifted ^ poly } else { shifted }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "result == 10")); // 5 << 1 = 10
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CRC step: 5 << 1 = 10 (no XOR)");
}

#[test]
fn polynomial_degree() {
    // CRC-8 polynomial has degree 8 (bit 8 set): e.g. 0x107 = 263
    let mut ctx = VerificationContext::new();
    for v in &["poly", "degree_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "poly == 263")); // 0x107
    ctx.push_obligation(ProofObligation::assume(
        "db_def",
        "degree_bit == (poly >> 8) & 1",
    ));
    ctx.push_obligation(ProofObligation::assert("bit8_set", "degree_bit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CRC-8: bit 8 of 0x107 is set");
}

#[test]
fn crc_of_zero_data() {
    // CRC of all-zero data with initial=0 is 0
    let mut ctx = VerificationContext::new();
    for v in &["initial", "data", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i", "initial == 0"));
    ctx.push_obligation(ProofObligation::assume("d", "data == 0"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == initial ^ data"));
    ctx.push_obligation(ProofObligation::assert("is_zero", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CRC(0, 0) = 0");
}

#[test]
fn crc_check_detects_error() {
    // Append CRC to data; any bit flip changes the check result
    let mut ctx = VerificationContext::new();
    for v in &["original_crc", "flipped_data_crc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("error_detected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oc", "original_crc == 42"));
    ctx.push_obligation(ProofObligation::assume("fc", "flipped_data_crc == 37"));
    ctx.push_obligation(ProofObligation::assume(
        "ed_def",
        "error_detected == if original_crc != flipped_data_crc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("detected", "error_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "different CRC → error detected");
}

#[test]
fn generator_polynomial_bits() {
    // CRC-32 polynomial: 0x04C11DB7 = 79764919
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("poly", u32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "poly == 79764919"));
    ctx.push_obligation(ProofObligation::assert("positive", "poly > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRC-32 poly is positive");
}

#[test]
fn reflect_byte_bit_0_to_7() {
    // Reflecting a byte: swap bits 0↔7, 1↔6, etc.
    // 0b10000001 = 129 → reflected = 129 (palindrome)
    let mut ctx = VerificationContext::new();
    for v in &["val", "reflected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 129"));
    ctx.push_obligation(ProofObligation::assume("ref_val", "reflected == 129"));
    ctx.push_obligation(ProofObligation::assert("palindrome", "reflected == val"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reflect(0x81) = 0x81 (palindrome)");
}

#[test]
fn xor_accumulate_two_bytes() {
    // XOR accumulate: acc ^= byte1; acc ^= byte2
    let mut ctx = VerificationContext::new();
    for v in &["acc", "byte1", "byte2", "after1", "after2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "acc == 0"));
    ctx.push_obligation(ProofObligation::assume("b1", "byte1 == 170")); // 0xAA
    ctx.push_obligation(ProofObligation::assume("b2", "byte2 == 85")); // 0x55
    ctx.push_obligation(ProofObligation::assume("a1_def", "after1 == acc ^ byte1"));
    ctx.push_obligation(ProofObligation::assume(
        "a2_def",
        "after2 == after1 ^ byte2",
    ));
    // 0 ^ 0xAA = 0xAA; 0xAA ^ 0x55 = 0xFF = 255
    ctx.push_obligation(ProofObligation::assert("is_255", "after2 == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0 ^ 0xAA ^ 0x55 = 0xFF");
}
