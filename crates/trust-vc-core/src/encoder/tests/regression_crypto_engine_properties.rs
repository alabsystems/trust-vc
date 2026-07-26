// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn aes_block_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("block_size_bits", u32_ty());
    ctx.declare_var_typed("block_size_bytes", u32_ty());
    // AES: always 128-bit (16-byte) blocks regardless of key size
    ctx.push_obligation(ProofObligation::assume("bsb", "block_size_bits == 128"));
    ctx.push_obligation(ProofObligation::assume("bsby", "block_size_bytes == 16"));
    ctx.push_obligation(ProofObligation::assert("bits", "block_size_bits == 128"));
    ctx.push_obligation(ProofObligation::assert("bytes", "block_size_bytes == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES: 128-bit = 16-byte block");
}

#[test]
fn key_expansion_rounds() {
    let mut ctx = VerificationContext::new();
    for v in &["key_bits", "num_rounds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AES rounds: 128→10, 192→12, 256→14
    ctx.push_obligation(ProofObligation::assume("kb", "key_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("nr", "num_rounds == 14"));
    ctx.push_obligation(ProofObligation::assert("is_14", "num_rounds == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES-256: 14 rounds");
}

#[test]
fn cbc_iv_requirement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("iv_provided", u32_ty());
    ctx.declare_var_typed("config_valid", i32_ty());
    // CBC mode requires IV; ECB does not. Modes: 0=ECB, 1=CBC, 2=CTR, 3=GCM
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1")); // CBC
    ctx.push_obligation(ProofObligation::assume("iv", "iv_provided == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "config_valid == if mode == 0 || iv_provided == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "config_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES-CBC: IV provided → config valid");
}

#[test]
fn gcm_tag_size() {
    let mut ctx = VerificationContext::new();
    for v in &["tag_bits", "min_tag_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tag_valid", i32_ty());
    // GCM: tag is 128 bits (recommended), min 32 bits
    ctx.push_obligation(ProofObligation::assume("tb", "tag_bits == 128"));
    ctx.push_obligation(ProofObligation::assume("mtb", "min_tag_bits == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "tv_def",
        "tag_valid == if tag_bits >= min_tag_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "tag_valid == 1"));
    ctx.push_obligation(ProofObligation::assert("full", "tag_bits == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GCM: 128-bit tag >= 32 min → valid");
}

#[test]
fn ctr_counter_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "blocks_processed", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CTR mode: counter increments per block
    ctx.push_obligation(ProofObligation::assume("c", "counter == 1"));
    ctx.push_obligation(ProofObligation::assume("bp", "blocks_processed == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == counter + blocks_processed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_101", "new_counter == 101"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AES-CTR: 1 + 100 = counter at 101");
}

#[test]
fn sha256_digest_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("digest_bits", u32_ty());
    ctx.declare_var_typed("digest_bytes", u32_ty());
    ctx.push_obligation(ProofObligation::assume("db", "digest_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("dby", "digest_bytes == 32"));
    ctx.push_obligation(ProofObligation::assert("bits", "digest_bits == 256"));
    ctx.push_obligation(ProofObligation::assert("bytes", "digest_bytes == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHA-256: 256 bits = 32 bytes digest");
}

#[test]
fn sha256_message_block() {
    let mut ctx = VerificationContext::new();
    for v in &["message_bytes", "block_size", "blocks_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // SHA-256 processes 512-bit (64-byte) blocks
    // 200 bytes → ceil(200/64) = 4 blocks (with padding)
    // Precompute: (200 + 64 - 1) / 64 = 263/64 = 4 (integer division)
    ctx.push_obligation(ProofObligation::assume("mb", "message_bytes == 200"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume("bn", "blocks_needed == 4")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4", "blocks_needed == 4"));
    ctx.push_obligation(ProofObligation::assert("positive", "blocks_needed > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SHA-256: 200 bytes → 4 blocks");
}

#[test]
fn hmac_key_padding() {
    let mut ctx = VerificationContext::new();
    for v in &["key_length", "block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_hash", i32_ty());
    // HMAC: if key > block_size, hash it first; otherwise pad with zeros
    ctx.push_obligation(ProofObligation::assume("kl", "key_length == 100")); // > 64
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "needs_hash == if key_length > block_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_hash == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HMAC: key 100 > block 64 → hash first");
}

#[test]
fn dma_transfer_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["src_addr", "dst_addr", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("both_aligned", i32_ty());
    // Crypto DMA requires word-aligned source and destination
    ctx.push_obligation(ProofObligation::assume("sa", "src_addr == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("da", "dst_addr == 536875008")); // 0x20001000
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 4")); // 32-bit aligned
    ctx.push_obligation(ProofObligation::assume(
        "ba_def",
        "both_aligned == if src_addr % alignment == 0 && dst_addr % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "both_aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "crypto DMA: src + dst both 4-byte aligned");
}

#[test]
fn rng_entropy_pool() {
    let mut ctx = VerificationContext::new();
    for v in &["entropy_bits", "min_entropy", "output_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // TRNG: entropy pool must have >= output bits of entropy
    ctx.push_obligation(ProofObligation::assume("eb", "entropy_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("me", "min_entropy == 128"));
    ctx.push_obligation(ProofObligation::assume("ob", "output_bits == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if entropy_bits >= output_bits && entropy_bits >= min_entropy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RNG: 256 bits entropy >= 128 output → sufficient");
}
