// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn compression_reduces_size() {
    let mut ctx = VerificationContext::new();
    for v in &["original", "compressed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "original == 1000"));
    ctx.push_obligation(ProofObligation::assume("c", "compressed == 400"));
    ctx.push_obligation(ProofObligation::assert("smaller", "compressed < original"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "400 < 1000: compression reduces size");
}

#[test]
fn compression_ratio_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["original", "compressed", "ratio_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "original == 1000"));
    ctx.push_obligation(ProofObligation::assume("c", "compressed == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "ratio_pct == compressed * 100 / original",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "ratio_pct == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "compression ratio: 400/1000 = 40%");
}

#[test]
fn space_savings() {
    let mut ctx = VerificationContext::new();
    for v in &["original", "compressed", "savings"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "original == 1000"));
    ctx.push_obligation(ProofObligation::assume("c", "compressed == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "savings == original - compressed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_600", "savings == 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "savings: 1000 - 400 = 600 bytes");
}

#[test]
fn decompression_restores_original() {
    let mut ctx = VerificationContext::new();
    for v in &["original_size", "decompressed_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("os", "original_size == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ds_def",
        "decompressed_size == original_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "decompressed_size == 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decompression restores original size");
}

#[test]
fn incompressible_data_no_expansion() {
    // Random data shouldn't expand much
    let mut ctx = VerificationContext::new();
    for v in &["original", "compressed", "overhead"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "original == 1000"));
    ctx.push_obligation(ProofObligation::assume("c", "compressed == 1010")); // slight expansion
    ctx.push_obligation(ProofObligation::assume(
        "oh_def",
        "overhead == compressed - original",
    ));
    ctx.push_obligation(ProofObligation::assert("small_overhead", "overhead <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 byte overhead <= 100 max");
}

#[test]
fn block_compression_total() {
    // Compress in blocks: total = sum of compressed blocks
    let mut ctx = VerificationContext::new();
    for v in &["block1", "block2", "block3", "total_compressed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b1", "block1 == 100"));
    ctx.push_obligation(ProofObligation::assume("b2", "block2 == 150"));
    ctx.push_obligation(ProofObligation::assume("b3", "block3 == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_compressed == block1 + block2 + block3",
    ));
    ctx.push_obligation(ProofObligation::assert("is_370", "total_compressed == 370"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 blocks: 100+150+120 = 370 compressed");
}

#[test]
fn dictionary_size_bound() {
    let mut ctx = VerificationContext::new();
    for v in &["dict_size", "max_dict"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_dict", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ds", "dict_size == 32768"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dict == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dict == if dict_size <= max_dict { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_dict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dict 32768 <= max 65536");
}

#[test]
fn run_length_encoding() {
    // RLE: 'AAABBC' → 3A2B1C → 6 chars become 6 encoded chars
    let mut ctx = VerificationContext::new();
    for v in &["run1_count", "run2_count", "run3_count", "total_runs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r1", "run1_count == 3"));
    ctx.push_obligation(ProofObligation::assume("r2", "run2_count == 2"));
    ctx.push_obligation(ProofObligation::assume("r3", "run3_count == 1"));
    ctx.push_obligation(ProofObligation::assume("tr_def", "total_runs == 3")); // 3 distinct runs
    ctx.push_obligation(ProofObligation::assert(
        "total_chars",
        "run1_count + run2_count + run3_count == 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RLE: 3+2+1 = 6 total characters");
}

#[test]
fn huffman_shorter_for_frequent() {
    // More frequent symbol gets shorter code
    let mut ctx = VerificationContext::new();
    for v in &["freq_a", "freq_b", "code_len_a", "code_len_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fa", "freq_a == 100")); // more frequent
    ctx.push_obligation(ProofObligation::assume("fb", "freq_b == 10")); // less frequent
    ctx.push_obligation(ProofObligation::assume("cla", "code_len_a == 2")); // shorter code
    ctx.push_obligation(ProofObligation::assume("clb", "code_len_b == 5")); // longer code
    ctx.push_obligation(ProofObligation::assert(
        "shorter",
        "code_len_a < code_len_b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Huffman: frequent symbol gets shorter code");
}

#[test]
fn lz77_match_length() {
    // Match: (distance, length) pair
    let mut ctx = VerificationContext::new();
    for v in &["match_distance", "match_length", "window_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_match", i32_ty());
    ctx.push_obligation(ProofObligation::assume("md", "match_distance == 100"));
    ctx.push_obligation(ProofObligation::assume("ml", "match_length == 15"));
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 32768"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_match == if match_distance <= window_size && match_length >= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LZ77: distance 100, length 15, valid match");
}
