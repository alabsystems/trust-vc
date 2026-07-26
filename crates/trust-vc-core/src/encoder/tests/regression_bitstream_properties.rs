// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bit_position_advances() {
    let mut ctx = VerificationContext::new();
    for v in &["pos", "bits_read", "new_pos"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pos == 10"));
    ctx.push_obligation(ProofObligation::assume("br", "bits_read == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "new_pos == pos + bits_read",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "new_pos == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bit position: 10 + 5 = 15");
}

#[test]
fn byte_offset_from_bit_position() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_pos", "byte_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "bit_pos == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "byte_offset == bit_pos / 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "byte_offset == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 20 → byte 2");
}

#[test]
fn bit_within_byte() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_pos", "bit_in_byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "bit_pos == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "bib_def",
        "bit_in_byte == bit_pos % 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "bit_in_byte == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 20 % 8 = 4 within byte");
}

#[test]
fn byte_aligned_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bit_pos", u32_ty());
    ctx.declare_var_typed("is_aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bp", "bit_pos == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_aligned == if bit_pos % 8 == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("aligned", "is_aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 16 is byte-aligned");
}

#[test]
fn read_n_bits_mask() {
    // Read 3 bits from value starting at bit 0: val & ((1 << n) - 1)
    let mut ctx = VerificationContext::new();
    for v in &["val", "n", "mask", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 29")); // 0b11101
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 3"));
    ctx.push_obligation(ProofObligation::assume("m_def", "mask == (1 << n) - 1")); // 0b111 = 7
    ctx.push_obligation(ProofObligation::assume("r_def", "result == val & mask"));
    // 29 & 7 = 5 (0b101)
    ctx.push_obligation(ProofObligation::assert("is_5", "result == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "read 3 bits from 29 = 5");
}

#[test]
fn write_preserves_other_bits() {
    // Write value into field, preserve surrounding bits
    // field at bits [4:6] of 0xFF (11111111)
    let mut ctx = VerificationContext::new();
    for v in &[
        "original",
        "field_val",
        "clear_mask",
        "cleared",
        "shifted",
        "result",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original == 255")); // 0xFF
    ctx.push_obligation(ProofObligation::assume("fv", "field_val == 5")); // 0b101
                                                                          // Clear bits [4:6]: mask = ~(0b111 << 4) & 0xFF = ~0x70 & 0xFF = 0x8F = 143
    ctx.push_obligation(ProofObligation::assume("cm", "clear_mask == 143"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "cleared == original & clear_mask",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sh_def",
        "shifted == field_val << 4",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == cleared | shifted",
    ));
    // 255 & 143 = 143; 5 << 4 = 80; 143 | 80 = 223 = 0xDF
    ctx.push_obligation(ProofObligation::assert("is_223", "result == 223"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "write field 5 into bits [4:6] of 0xFF = 0xDF");
}

#[test]
fn total_bits_is_bytes_times_8() {
    let mut ctx = VerificationContext::new();
    for v in &["bytes", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "bytes == 100"));
    ctx.push_obligation(ProofObligation::assume("tb_def", "total_bits == bytes * 8"));
    ctx.push_obligation(ProofObligation::assert("is_800", "total_bits == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 bytes = 800 bits");
}

#[test]
fn remaining_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["total_bits", "pos", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_bits == 800"));
    ctx.push_obligation(ProofObligation::assume("p", "pos == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == total_bits - pos",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "remaining == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "800 - 300 = 500 remaining bits");
}

#[test]
fn variable_length_field_size() {
    // Exp-Golomb: value n encoded in 2*floor(log2(n+1))+1 bits
    // n=6: floor(log2(7)) = 2, size = 2*2+1 = 5 bits
    let mut ctx = VerificationContext::new();
    for v in &["n", "encoded_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 6"));
    ctx.push_obligation(ProofObligation::assume("eb_val", "encoded_bits == 5"));
    ctx.push_obligation(ProofObligation::assert("is_5", "encoded_bits == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exp-golomb(6) = 5 bits");
}

#[test]
fn padding_to_byte_boundary() {
    // Padding needed = (8 - (pos % 8)) % 8
    let mut ctx = VerificationContext::new();
    for v in &["pos", "pad_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pos == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "pb_def",
        "pad_bits == (8 - (pos % 8)) % 8",
    ));
    // (8 - 5) % 8 = 3
    ctx.push_obligation(ProofObligation::assert("is_3", "pad_bits == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pad bit 13 to byte: 3 bits");
}
