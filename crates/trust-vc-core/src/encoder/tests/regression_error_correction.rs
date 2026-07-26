// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn hamming_distance_identical() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "xor_result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 42"));
    ctx.push_obligation(ProofObligation::assume("xor_def", "xor_result == a ^ b"));
    ctx.push_obligation(ProofObligation::assert("zero", "xor_result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "identical words: hamming distance = 0");
}

#[test]
fn hamming_distance_one_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "xor_result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 5 = 0b101, 4 = 0b100, differ in bit 0
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("xor_def", "xor_result == a ^ b"));
    ctx.push_obligation(ProofObligation::assert("is_1", "xor_result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 ^ 4 = 1 (single bit difference)");
}

#[test]
fn triple_repetition_majority() {
    // Triple repetition code: majority vote of 3 copies
    let mut ctx = VerificationContext::new();
    for v in &["b0", "b1", "b2", "decoded"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // One bit flipped: (1, 0, 1) → majority = 1
    ctx.push_obligation(ProofObligation::assume("b0_val", "b0 == 1"));
    ctx.push_obligation(ProofObligation::assume("b1_val", "b1 == 0"));
    ctx.push_obligation(ProofObligation::assume("b2_val", "b2 == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "decoded_def",
        "decoded == if b0 + b1 + b2 >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("corrected", "decoded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "triple repetition: (1,0,1) → 1 by majority");
}

#[test]
fn parity_check_even() {
    let mut ctx = VerificationContext::new();
    for v in &["d0", "d1", "d2", "parity", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d0_val", "d0 == 1"));
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 0"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 1"));
    // Even parity: parity bit makes total even
    ctx.push_obligation(ProofObligation::assume(
        "parity_def",
        "parity == (d0 + d1 + d2) & 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == d0 + d1 + d2 + parity",
    ));
    // 1+0+1 = 2, parity = 0, total = 2 (even)
    ctx.push_obligation(ProofObligation::assert("is_even", "total & 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "parity check: total is even");
}

#[test]
fn single_error_detectable() {
    // With parity, flipping one bit changes parity
    let mut ctx = VerificationContext::new();
    for v in &["data", "parity_orig", "data_err", "parity_err"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "data == 6"));
    ctx.push_obligation(ProofObligation::assume("po", "parity_orig == data & 1"));
    // Flip one bit: 6 (0b110) → 7 (0b111)
    ctx.push_obligation(ProofObligation::assume("de", "data_err == 7"));
    ctx.push_obligation(ProofObligation::assume("pe", "parity_err == data_err & 1"));
    ctx.push_obligation(ProofObligation::assert(
        "different",
        "parity_orig != parity_err",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "single bit flip changes parity");
}

#[test]
fn syndrome_zero_means_no_error() {
    // In Hamming code, syndrome = 0 means no error
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("syndrome", u32_ty());
    ctx.declare_var_typed("has_error", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "syndrome == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "err_def",
        "has_error == if syndrome == 0 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_error", "has_error == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "syndrome 0 → no error");
}

#[test]
fn syndrome_nonzero_locates_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("syndrome", u32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "syndrome == 3"));
    // Syndrome value is the position of the error (1-indexed)
    ctx.push_obligation(ProofObligation::assert("locates", "syndrome > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nonzero syndrome locates error at position 3");
}

#[test]
fn crc_remainder_zero_no_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("remainder", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "remainder == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_def",
        "valid == if remainder == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRC remainder 0 = valid message");
}

#[test]
fn redundancy_ratio() {
    // k data bits, n total bits, redundancy = n - k
    let mut ctx = VerificationContext::new();
    for v in &["k", "n", "redundancy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k_val", "k == 4"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 7"));
    ctx.push_obligation(ProofObligation::assume("red_def", "redundancy == n - k"));
    ctx.push_obligation(ProofObligation::assert("is_3", "redundancy == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming(7,4): 3 redundancy bits");
}

#[test]
fn bit_flip_correction() {
    // Correct a known error position by flipping the bit
    let mut ctx = VerificationContext::new();
    for v in &["received", "error_mask", "corrected", "original"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original == 10"));
    // Error at bit 1: flip bit 1 of original
    ctx.push_obligation(ProofObligation::assume("em", "error_mask == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "recv",
        "received == original ^ error_mask",
    ));
    // Correction: flip the error bit again
    ctx.push_obligation(ProofObligation::assume(
        "corr",
        "corrected == received ^ error_mask",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "recovered",
        "corrected == original",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR correction recovers original");
}
