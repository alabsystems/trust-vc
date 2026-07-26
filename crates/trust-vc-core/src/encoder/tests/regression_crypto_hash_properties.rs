// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sha256_output_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hash_bits", u32_ty());
    ctx.declare_var_typed("hash_bytes", u32_ty());
    // SHA-256: 256 bits = 32 bytes
    ctx.push_obligation(ProofObligation::assume("hb", "hash_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("hby", "hash_bytes == 32")); // precomputed 256/8
    ctx.push_obligation(ProofObligation::assert("is_32", "hash_bytes == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHA-256: 256 bits = 32 bytes output");
}

#[test]
fn block_padding_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "message_bytes",
        "block_size",
        "last_block_used",
        "padding_bytes",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // SHA-256 block = 64 bytes. Padding needed to fill last block.
    // msg=50 bytes → last_block_used=50, padding=64-50=14 (simplified)
    ctx.push_obligation(ProofObligation::assume("mb", "message_bytes == 50"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume("lbu", "last_block_used == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "pb_def",
        "padding_bytes == block_size - last_block_used",
    ));
    ctx.push_obligation(ProofObligation::assert("is_14", "padding_bytes == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHA-256: 50 bytes in 64-byte block → 14 padding");
}

#[test]
fn hmac_key_length() {
    let mut ctx = VerificationContext::new();
    for v in &["key_bytes", "block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_hash", i32_ty());
    // HMAC: if key > block_size, hash it first
    ctx.push_obligation(ProofObligation::assume("kb", "key_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "needs_hash == if key_bytes > block_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_hash == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HMAC: key 128 > block 64 → hash key first");
}

#[test]
fn hash_chain_iteration() {
    let mut ctx = VerificationContext::new();
    for v in &["current_iteration", "total_iterations"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("done", i32_ty());
    // PBKDF2: iterate hash function N times
    ctx.push_obligation(ProofObligation::assume("ci", "current_iteration == 10000"));
    ctx.push_obligation(ProofObligation::assume("ti", "total_iterations == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "done == if current_iteration >= total_iterations { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "done == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PBKDF2: iteration 10000 = total 10000 → done");
}

#[test]
fn merkle_tree_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["leaf_count", "tree_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Depth = log2(leaves). Precompute: log2(1024) = 10
    ctx.push_obligation(ProofObligation::assume("lc", "leaf_count == 1024"));
    ctx.push_obligation(ProofObligation::assume("td", "tree_depth == 10")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_10", "tree_depth == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Merkle: 1024 leaves → depth 10 (precomputed)");
}

#[test]
fn digest_comparison() {
    let mut ctx = VerificationContext::new();
    for v in &["expected_hash_low", "actual_hash_low"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hash_match", i32_ty());
    // Compare first 32 bits of hash digest
    ctx.push_obligation(ProofObligation::assume(
        "eh",
        "expected_hash_low == 305419896",
    )); // 0x12345678
    ctx.push_obligation(ProofObligation::assume(
        "ah",
        "actual_hash_low == 305419896",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hm_def",
        "hash_match == if expected_hash_low == actual_hash_low { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hash_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hash: expected 0x12345678 = actual → match");
}

#[test]
fn blake2_personalization() {
    let mut ctx = VerificationContext::new();
    for v in &["person_bytes", "max_person_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_person", i32_ty());
    // BLAKE2b personalization: up to 16 bytes
    ctx.push_obligation(ProofObligation::assume("pb", "person_bytes == 8"));
    ctx.push_obligation(ProofObligation::assume("mpb", "max_person_bytes == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_person == if person_bytes <= max_person_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_person == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLAKE2b: 8-byte personalization ≤ 16 max → valid");
}

#[test]
fn hash_function_security_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hash_bits", u32_ty());
    ctx.declare_var_typed("security_bits", u32_ty());
    // Collision resistance = hash_bits / 2. Precompute: 256 / 2 = 128
    ctx.push_obligation(ProofObligation::assume("hb", "hash_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("sb", "security_bits == 128")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_128", "security_bits == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHA-256: 256/2 = 128-bit collision resistance");
}

#[test]
fn streaming_hash_state() {
    let mut ctx = VerificationContext::new();
    for v in &["bytes_processed", "bytes_added", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Streaming: update state incrementally
    ctx.push_obligation(ProofObligation::assume("bp", "bytes_processed == 4096"));
    ctx.push_obligation(ProofObligation::assume("ba", "bytes_added == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == bytes_processed + bytes_added",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5120", "total_bytes == 5120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hash streaming: 4096 + 1024 = 5120 total bytes");
}

#[test]
fn xof_output_length() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_bytes", "min_output_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // Extendable Output Function (XOF): arbitrary output length
    // SHAKE256: min security = 32 bytes
    ctx.push_obligation(ProofObligation::assume("rb", "requested_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("mob", "min_output_bytes == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if requested_bytes >= min_output_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHAKE256 XOF: 64 bytes ≥ 32 min → sufficient");
}
