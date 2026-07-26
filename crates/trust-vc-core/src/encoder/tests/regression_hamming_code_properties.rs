// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn hamming_7_4_codeword_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "parity_bits", "codeword_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 4"));
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cb_def",
        "codeword_bits == data_bits + parity_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "codeword_bits == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming(7,4): 4 data + 3 parity = 7 bits");
}

#[test]
fn single_error_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["parity_bits", "detectable_errors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hamming code detects up to 1 error (minimum distance = 3 → d-1 = 2 detectable, 1 correctable)
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 3"));
    ctx.push_obligation(ProofObligation::assume("de", "detectable_errors == 1")); // single error correction
    ctx.push_obligation(ProofObligation::assert("is_1", "detectable_errors == 1"));
    ctx.push_obligation(ProofObligation::assert("positive", "detectable_errors > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming: corrects 1 error");
}

#[test]
fn syndrome_identifies_position() {
    // Syndrome = 0 means no error; nonzero syndrome = error bit position
    let mut ctx = VerificationContext::new();
    for v in &["syndrome", "error_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_error", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "syndrome == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "error_position == syndrome",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "he_def",
        "has_error == if syndrome != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pos_5", "error_position == 5"));
    ctx.push_obligation(ProofObligation::assert("yes", "has_error == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "syndrome 5 → error at position 5");
}

#[test]
fn parity_check_equations() {
    // In Hamming(7,4), parity bit positions are 1, 2, 4
    let mut ctx = VerificationContext::new();
    for v in &["p1_pos", "p2_pos", "p4_pos", "total_parity_positions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p1", "p1_pos == 1"));
    ctx.push_obligation(ProofObligation::assume("p2", "p2_pos == 2"));
    ctx.push_obligation(ProofObligation::assume("p4", "p4_pos == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tpp_def",
        "total_parity_positions == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("p1_is_pow2", "p1_pos == 1"));
    ctx.push_obligation(ProofObligation::assert("p2_is_pow2", "p2_pos == 2"));
    ctx.push_obligation(ProofObligation::assert("p4_is_pow2", "p4_pos == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "parity positions: 1, 2, 4 (powers of 2)");
}

#[test]
fn hamming_bound() {
    // 2^r >= n + 1 where r = parity bits, n = codeword length
    let mut ctx = VerificationContext::new();
    for v in &["parity_bits", "codeword_len", "two_pow_r"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("satisfies_bound", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 3"));
    ctx.push_obligation(ProofObligation::assume("cl", "codeword_len == 7"));
    ctx.push_obligation(ProofObligation::assume("tpr", "two_pow_r == 8")); // 2^3 = 8
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "satisfies_bound == if two_pow_r >= codeword_len + 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "satisfies_bound == 1")); // 8 >= 8
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming bound: 2^3 = 8 >= 7 + 1");
}

#[test]
fn secded_extra_parity() {
    // SECDED adds one overall parity bit to Hamming code
    let mut ctx = VerificationContext::new();
    for v in &["hamming_bits", "extra_parity", "secded_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hb", "hamming_bits == 7"));
    ctx.push_obligation(ProofObligation::assume("ep", "extra_parity == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "secded_bits == hamming_bits + extra_parity",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "secded_bits == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SECDED: 7 Hamming + 1 overall = 8 bits");
}

#[test]
fn code_rate_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "codeword_bits", "rate_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 4"));
    ctx.push_obligation(ProofObligation::assume("cb", "codeword_bits == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "rp_def",
        "rate_pct == data_bits * 100 / codeword_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_57", "rate_pct == 57")); // 4/7 ≈ 57%
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Hamming(7,4) rate: 4*100/7 ≈ 57%");
}

#[test]
fn extended_hamming_15_11() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "parity_bits", "codeword_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 11"));
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 4")); // 2^4 - 1 = 15
    ctx.push_obligation(ProofObligation::assume(
        "cb_def",
        "codeword_bits == data_bits + parity_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "codeword_bits == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming(15,11): 11 data + 4 parity = 15 bits");
}

#[test]
fn minimum_distance() {
    // Hamming codes have minimum distance 3
    let mut ctx = VerificationContext::new();
    for v in &[
        "min_distance",
        "correction_capability",
        "detection_capability",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("md", "min_distance == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "correction_capability == (min_distance - 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dc_def",
        "detection_capability == min_distance - 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_1",
        "correction_capability == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("dc_2", "detection_capability == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "d_min=3: correct 1, detect 2 errors");
}

#[test]
fn error_correction_flips_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["received_word", "error_mask", "corrected_word"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // XOR with single-bit error mask flips the error bit
    ctx.push_obligation(ProofObligation::assume("rw", "received_word == 107")); // has error
    ctx.push_obligation(ProofObligation::assume("em", "error_mask == 4")); // error at bit 2
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "corrected_word == received_word ^ error_mask",
    ));
    // 107 XOR 4 = 111 (0b1101011 ^ 0b0000100 = 0b1101111)
    ctx.push_obligation(ProofObligation::assert("is_111", "corrected_word == 111"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "correction: 107 XOR 4 = 111");
}
