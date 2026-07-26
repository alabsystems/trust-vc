// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rle_single_run() {
    // Run-length encoding: "AAAA" → (A, 4)
    let mut ctx = VerificationContext::new();
    for v in &["symbol", "count", "original_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sym", "symbol == 65"));
    ctx.push_obligation(ProofObligation::assume("cnt", "count == 4"));
    ctx.push_obligation(ProofObligation::assume("orig_def", "original_len == count"));
    ctx.push_obligation(ProofObligation::assert("compressed", "original_len == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RLE: AAAA → (A, 4), original length 4");
}

#[test]
fn rle_two_runs_shorter() {
    // "AAABBB" (6 chars) → (A,3)(B,3) (2 pairs = 4 values)
    let mut ctx = VerificationContext::new();
    for v in &[
        "run1_count",
        "run2_count",
        "original_len",
        "compressed_pairs",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r1", "run1_count == 3"));
    ctx.push_obligation(ProofObligation::assume("r2", "run2_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "orig_def",
        "original_len == run1_count + run2_count",
    ));
    ctx.push_obligation(ProofObligation::assume("comp_def", "compressed_pairs == 2"));
    ctx.push_obligation(ProofObligation::assert("orig_is_6", "original_len == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer_pairs",
        "compressed_pairs < original_len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RLE compresses AAABBB from 6 to 2 pairs");
}

#[test]
fn rle_no_compression_alternating() {
    // "ABAB" (4 chars) → (A,1)(B,1)(A,1)(B,1) (4 pairs = 8 values, worse!)
    let mut ctx = VerificationContext::new();
    for v in &["original_len", "num_runs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original_len == 4"));
    ctx.push_obligation(ProofObligation::assume("runs", "num_runs == 4"));
    // Each run is length 1, so num_runs == original_len (no compression)
    ctx.push_obligation(ProofObligation::assert(
        "no_compression",
        "num_runs == original_len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alternating sequence: RLE doesn't compress");
}

#[test]
fn dictionary_lookup_size() {
    // Dictionary with 256 entries, each entry referenced by 1 byte
    let mut ctx = VerificationContext::new();
    for v in &["dict_size", "ref_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ds", "dict_size == 256"));
    ctx.push_obligation(ProofObligation::assume("rb", "ref_bits == 8"));
    // 2^8 = 256 entries addressable
    ctx.push_obligation(ProofObligation::assert("fits", "dict_size <= 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8-bit reference addresses 256 dictionary entries");
}

#[test]
fn compression_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["original", "compressed", "saved"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original == 100"));
    ctx.push_obligation(ProofObligation::assume("comp", "compressed == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "saved_def",
        "saved == original - compressed",
    ));
    ctx.push_obligation(ProofObligation::assert("saved_60", "saved == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 → 40: saved 60 bytes");
}

#[test]
fn decompression_recovers_original_size() {
    let mut ctx = VerificationContext::new();
    for v in &["original_size", "compressed_size", "decompressed_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original_size == 1000"));
    ctx.push_obligation(ProofObligation::assume("comp", "compressed_size == 400"));
    // Lossless: decompressed == original
    ctx.push_obligation(ProofObligation::assume(
        "decomp",
        "decompressed_size == original_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "matches",
        "decompressed_size == 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lossless decompression recovers original size");
}

#[test]
fn huffman_prefix_code_lengths() {
    // In Huffman coding, more frequent symbols get shorter codes
    let mut ctx = VerificationContext::new();
    for v in &["freq_a", "freq_b", "len_a", "len_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fa", "freq_a == 80"));
    ctx.push_obligation(ProofObligation::assume("fb", "freq_b == 20"));
    ctx.push_obligation(ProofObligation::assume("la", "len_a == 1"));
    ctx.push_obligation(ProofObligation::assume("lb", "len_b == 3"));
    // Higher frequency → shorter code
    ctx.push_obligation(ProofObligation::assert("shorter", "len_a < len_b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Huffman: freq 80 → len 1, freq 20 → len 3");
}

#[test]
fn block_size_total() {
    // Blocked compression: total = num_blocks * block_size + remainder
    let mut ctx = VerificationContext::new();
    for v in &["total", "block_size", "num_blocks", "remainder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "total == 1000"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume("nb", "num_blocks == 15"));
    ctx.push_obligation(ProofObligation::assume("rem", "remainder == 40"));
    // 15 * 64 + 40 = 960 + 40 = 1000
    ctx.push_obligation(ProofObligation::assume(
        "check",
        "num_blocks * block_size + remainder == total",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conserved",
        "num_blocks * block_size + remainder == 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "15 * 64 + 40 = 1000");
}

#[test]
fn delta_encoding_differences() {
    // Delta encoding: store differences instead of absolute values
    // [10, 13, 15, 20] → [10, 3, 2, 5]
    let mut ctx = VerificationContext::new();
    for v in &["v0", "v1", "v2", "v3", "d0", "d1", "d2", "d3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v0_val", "v0 == 10"));
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 13"));
    ctx.push_obligation(ProofObligation::assume("v2_val", "v2 == 15"));
    ctx.push_obligation(ProofObligation::assume("v3_val", "v3 == 20"));
    ctx.push_obligation(ProofObligation::assume("d0_def", "d0 == v0"));
    ctx.push_obligation(ProofObligation::assume("d1_def", "d1 == v1 - v0"));
    ctx.push_obligation(ProofObligation::assume("d2_def", "d2 == v2 - v1"));
    ctx.push_obligation(ProofObligation::assume("d3_def", "d3 == v3 - v2"));
    ctx.push_obligation(ProofObligation::assert("d0_10", "d0 == 10"));
    ctx.push_obligation(ProofObligation::assert("d1_3", "d1 == 3"));
    ctx.push_obligation(ProofObligation::assert("d2_2", "d2 == 2"));
    ctx.push_obligation(ProofObligation::assert("d3_5", "d3 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delta encoding: [10,13,15,20] → [10,3,2,5]");
}

#[test]
fn delta_decode_recovers_original() {
    // Decode: cumulative sum of deltas
    let mut ctx = VerificationContext::new();
    for v in &["d0", "d1", "d2", "r0", "r1", "r2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d0_val", "d0 == 10"));
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 3"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 2"));
    ctx.push_obligation(ProofObligation::assume("r0_def", "r0 == d0"));
    ctx.push_obligation(ProofObligation::assume("r1_def", "r1 == r0 + d1"));
    ctx.push_obligation(ProofObligation::assume("r2_def", "r2 == r1 + d2"));
    ctx.push_obligation(ProofObligation::assert("r0_10", "r0 == 10"));
    ctx.push_obligation(ProofObligation::assert("r1_13", "r1 == 13"));
    ctx.push_obligation(ProofObligation::assert("r2_15", "r2 == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delta decode: [10,3,2] → [10,13,15]");
}
