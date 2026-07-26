// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn block_size_128_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["block_bits", "block_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bb", "block_bits == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "bby_def",
        "block_bytes == block_bits / 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "block_bytes == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AES block: 128 bits / 8 = 16 bytes");
}

#[test]
fn key_size_determines_rounds() {
    let mut ctx = VerificationContext::new();
    for v in &["key_bits", "rounds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AES-128: 10 rounds, AES-192: 12 rounds, AES-256: 14 rounds
    ctx.push_obligation(ProofObligation::assume("kb", "key_bits == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "rounds == if key_bits == 128 { 10 } else { if key_bits == 192 { 12 } else { 14 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_14", "rounds == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES-256: 14 rounds");
}

#[test]
fn round_key_expansion_count() {
    let mut ctx = VerificationContext::new();
    for v in &["rounds", "round_keys_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Need rounds + 1 round keys (initial + one per round)
    ctx.push_obligation(ProofObligation::assume("r", "rounds == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "rkn_def",
        "round_keys_needed == rounds + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11", "round_keys_needed == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES-128: 10 rounds → 11 round keys");
}

#[test]
fn state_matrix_dimensions() {
    let mut ctx = VerificationContext::new();
    for v in &["rows", "cols", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "rows == 4"));
    ctx.push_obligation(ProofObligation::assume("c", "cols == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == rows * cols",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "total_bytes == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AES state: 4×4 = 16 bytes");
}

#[test]
fn xor_inverse_property() {
    // XOR is its own inverse: (a ^ b) ^ b == a
    let mut ctx = VerificationContext::new();
    for v in &["plaintext", "key", "ciphertext", "decrypted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pt", "plaintext == 170")); // 0xAA
    ctx.push_obligation(ProofObligation::assume("k", "key == 85")); // 0x55
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "ciphertext == plaintext ^ key",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dec_def",
        "decrypted == ciphertext ^ key",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "roundtrip",
        "decrypted == plaintext",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR roundtrip: (0xAA ^ 0x55) ^ 0x55 == 0xAA");
}

#[test]
fn ctr_mode_counter_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["nonce", "counter", "block_input", "next_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n", "nonce == 1000"));
    ctx.push_obligation(ProofObligation::assume("c", "counter == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "bi_def",
        "block_input == nonce + counter",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "next_counter == counter + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("bi_1005", "block_input == 1005"));
    ctx.push_obligation(ProofObligation::assert("nc_6", "next_counter == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CTR mode: nonce+5=1005, next counter=6");
}

#[test]
fn cbc_chain_length() {
    let mut ctx = VerificationContext::new();
    for v in &["message_bytes", "block_size", "num_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mb", "message_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "num_blocks == message_bytes / block_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "num_blocks == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CBC: 64 / 16 = 4 blocks");
}

#[test]
fn pkcs7_padding_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_len", "block_size", "remainder", "padding_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dl", "data_len == 50"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "rem_def",
        "remainder == data_len % block_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pl_def",
        "padding_len == if remainder == 0 { block_size } else { block_size - remainder }",
    ));
    // 50 % 16 = 2, so padding = 16 - 2 = 14
    ctx.push_obligation(ProofObligation::assert("is_14", "padding_len == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PKCS7: 50 mod 16 = 2, padding = 14");
}

#[test]
fn gcm_tag_size() {
    let mut ctx = VerificationContext::new();
    for v in &["ciphertext_len", "tag_bytes", "output_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cl", "ciphertext_len == 64"));
    ctx.push_obligation(ProofObligation::assume("tb", "tag_bytes == 16")); // 128-bit tag
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "output_len == ciphertext_len + tag_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "output_len == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GCM: 64 ciphertext + 16 tag = 80 bytes");
}

#[test]
fn key_schedule_word_count() {
    let mut ctx = VerificationContext::new();
    for v in &["round_keys", "words_per_key", "total_words"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rk", "round_keys == 11")); // AES-128
    ctx.push_obligation(ProofObligation::assume("wpk", "words_per_key == 4")); // 4 32-bit words
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_words == round_keys * words_per_key",
    ));
    ctx.push_obligation(ProofObligation::assert("is_44", "total_words == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "key schedule: 11 × 4 = 44 words");
}
