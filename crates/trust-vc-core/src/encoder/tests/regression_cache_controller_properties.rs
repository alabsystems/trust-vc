// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cache_line_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "line_size", "offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Extract byte offset within a 64-byte cache line
    ctx.push_obligation(ProofObligation::assume("a", "address == 4100")); // 0x1004
    ctx.push_obligation(ProofObligation::assume("ls", "line_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "offset == address % line_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "offset == 4")); // 4100 mod 64 = 4
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache: 4100 mod 64 = 4 offset");
}

#[test]
fn set_index_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["line_address", "num_sets", "set_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Set index = (address / line_size) mod num_sets — precomputed
    // address 4100 / 64 = line 64, 64 mod 128 = 64
    ctx.push_obligation(ProofObligation::assume("la", "line_address == 64"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_sets == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "si_def",
        "set_index == line_address % num_sets",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "set_index == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache: line 64 mod 128 sets = set 64");
}

#[test]
fn way_selection_lru() {
    let mut ctx = VerificationContext::new();
    for v in &["way0_age", "way1_age", "way2_age", "way3_age"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("evict_way", u32_ty());
    // 4-way set-associative: evict oldest (highest age)
    ctx.push_obligation(ProofObligation::assume("w0", "way0_age == 3"));
    ctx.push_obligation(ProofObligation::assume("w1", "way1_age == 7")); // oldest
    ctx.push_obligation(ProofObligation::assume("w2", "way2_age == 1"));
    ctx.push_obligation(ProofObligation::assume("w3", "way3_age == 5"));
    // Precomputed: way1 has highest age
    ctx.push_obligation(ProofObligation::assume("ew", "evict_way == 1"));
    ctx.push_obligation(ProofObligation::assert("is_1", "evict_way == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache LRU: way1 (age 7) evicted");
}

#[test]
fn write_back_dirty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dirty_bit", u32_ty());
    ctx.declare_var_typed("evicting", u32_ty());
    ctx.declare_var_typed("needs_writeback", i32_ty());
    // Write-back: dirty line must be written to memory on eviction
    ctx.push_obligation(ProofObligation::assume("db", "dirty_bit == 1"));
    ctx.push_obligation(ProofObligation::assume("ev", "evicting == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nw_def",
        "needs_writeback == if dirty_bit == 1 && evicting == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_writeback == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache: dirty + evicting → writeback");
}

#[test]
fn cache_hit_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tag_match", u32_ty());
    ctx.declare_var_typed("valid_bit", u32_ty());
    ctx.declare_var_typed("is_hit", i32_ty());
    // Hit = tag matches AND line is valid
    ctx.push_obligation(ProofObligation::assume("tm", "tag_match == 1"));
    ctx.push_obligation(ProofObligation::assume("vb", "valid_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_hit == if tag_match == 1 && valid_bit == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_hit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache: tag match + valid → hit");
}

#[test]
fn total_cache_size() {
    let mut ctx = VerificationContext::new();
    for v in &["num_sets", "ways", "line_size_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 128 sets × 4 ways × 64 bytes = 32768 bytes = 32KB
    // Precompute intermediate: 128 * 4 = 512 lines
    ctx.declare_var_typed("total_lines", u32_ty());
    ctx.declare_var_typed("total_bytes", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ns", "num_sets == 128"));
    ctx.push_obligation(ProofObligation::assume("w", "ways == 4"));
    ctx.push_obligation(ProofObligation::assume("ls", "line_size_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_lines == num_sets * ways",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == total_lines * line_size_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32768", "total_bytes == 32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache: 128×4×64 = 32768 bytes");
}

#[test]
fn miss_penalty_cycles() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_latency", "transfer_cycles", "total_penalty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Miss penalty = bus latency + burst transfer cycles
    ctx.push_obligation(ProofObligation::assume("bl", "bus_latency == 10"));
    ctx.push_obligation(ProofObligation::assume("tc", "transfer_cycles == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_penalty == bus_latency + transfer_cycles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_18", "total_penalty == 18"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache miss: 10 + 8 = 18 cycle penalty");
}

#[test]
fn prefetch_stream_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["consecutive_misses", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("prefetch_active", i32_ty());
    // Activate prefetch after N consecutive misses in same direction
    ctx.push_obligation(ProofObligation::assume("cm", "consecutive_misses == 4"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "prefetch_active == if consecutive_misses >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "prefetch_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache prefetch: 4 >= 3 → active");
}

#[test]
fn invalidation_protocol() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("remote_write", u32_ty());
    ctx.declare_var_typed("local_state", u32_ty());
    ctx.declare_var_typed("new_state", u32_ty());
    // MESI: Shared line invalidated by remote write → Invalid (state 0)
    // States: 0=Invalid, 1=Shared, 2=Exclusive, 3=Modified
    ctx.push_obligation(ProofObligation::assume("rw", "remote_write == 1"));
    ctx.push_obligation(ProofObligation::assume("ls", "local_state == 1")); // Shared
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_state == if remote_write == 1 && local_state == 1 { 0 } else { local_state }",
    ));
    ctx.push_obligation(ProofObligation::assert("invalid", "new_state == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MESI: Shared + remote write → Invalid");
}

#[test]
fn cache_partitioning() {
    let mut ctx = VerificationContext::new();
    for v in &["total_ways", "core0_ways", "core1_ways", "remaining_ways"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_partition", i32_ty());
    // Cache partitioning: allocate ways per core, ensure none left unassigned
    ctx.push_obligation(ProofObligation::assume("tw", "total_ways == 8"));
    ctx.push_obligation(ProofObligation::assume("c0", "core0_ways == 3"));
    ctx.push_obligation(ProofObligation::assume("c1", "core1_ways == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "rw_def",
        "remaining_ways == total_ways - core0_ways - core1_ways",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_partition == if remaining_ways == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "none_wasted",
        "remaining_ways == 0",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_partition == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache partition: 3 + 5 = 8 ways, none wasted");
}
