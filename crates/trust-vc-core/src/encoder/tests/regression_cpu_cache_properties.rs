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
    ctx.push_obligation(ProofObligation::assume("a", "address == 1000"));
    ctx.push_obligation(ProofObligation::assume("ls", "line_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "offset == address % line_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "offset == 40")); // 1000 mod 64 = 40
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache line offset: 1000 mod 64 = 40");
}

#[test]
fn cache_set_index() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "line_size", "num_sets", "set_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "address == 1024"));
    ctx.push_obligation(ProofObligation::assume("ls", "line_size == 64"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_sets == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "si_def",
        "set_index == (address / line_size) % num_sets",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "set_index == 0")); // (1024/64) % 16 = 16 % 16 = 0
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache set: (1024/64) % 16 = 0");
}

#[test]
fn cache_tag_extraction() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "line_size", "num_sets", "tag"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "address == 4096"));
    ctx.push_obligation(ProofObligation::assume("ls", "line_size == 64"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_sets == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "tag == address / (line_size * num_sets)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "tag == 1")); // 4096 / (64*64) = 1
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache tag: 4096 / 4096 = 1");
}

#[test]
fn hit_rate_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["hits", "total_accesses", "hit_rate_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hits == 90"));
    ctx.push_obligation(ProofObligation::assume("ta", "total_accesses == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "hr_def",
        "hit_rate_pct == hits * 100 / total_accesses",
    ));
    ctx.push_obligation(ProofObligation::assert("is_90", "hit_rate_pct == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hit rate: 90/100 * 100 = 90%");
}

#[test]
fn write_back_dirty_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dirty", i32_ty());
    ctx.declare_var_typed("written", i32_ty());
    ctx.declare_var_typed("needs_writeback", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "dirty == 1"));
    ctx.push_obligation(ProofObligation::assume("w", "written == 0")); // not yet written back
    ctx.push_obligation(ProofObligation::assume(
        "nw_def",
        "needs_writeback == if dirty == 1 && written == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wb", "needs_writeback == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dirty && !written → needs writeback");
}

#[test]
fn associativity_ways() {
    let mut ctx = VerificationContext::new();
    for v in &["cache_size", "line_size", "num_sets", "ways"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cs", "cache_size == 32768")); // 32KB
    ctx.push_obligation(ProofObligation::assume("ls", "line_size == 64"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_sets == 64"));
    // ways = cache_size / (line_size * num_sets)
    ctx.push_obligation(ProofObligation::assume(
        "w_def",
        "ways == cache_size / (line_size * num_sets)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "ways == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "associativity: 32768 / (64*64) = 8 ways");
}

#[test]
fn lru_eviction_age() {
    let mut ctx = VerificationContext::new();
    for v in &["access_time", "current_time", "age"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("at", "access_time == 100"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "age == current_time - access_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "age == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU age: 500 - 100 = 400");
}

#[test]
fn cache_miss_penalty() {
    let mut ctx = VerificationContext::new();
    for v in &["l1_latency", "l2_latency", "mem_latency", "miss_penalty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l1", "l1_latency == 1"));
    ctx.push_obligation(ProofObligation::assume("l2", "l2_latency == 10"));
    ctx.push_obligation(ProofObligation::assume("ml", "mem_latency == 100"));
    // L1 miss, L2 miss → mem access
    ctx.push_obligation(ProofObligation::assume(
        "mp_def",
        "miss_penalty == l1_latency + l2_latency + mem_latency",
    ));
    ctx.push_obligation(ProofObligation::assert("is_111", "miss_penalty == 111"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "miss penalty: 1 + 10 + 100 = 111 cycles");
}

#[test]
fn prefetch_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["stride", "lookahead", "prefetch_addr", "current_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "stride == 64"));
    ctx.push_obligation(ProofObligation::assume("l", "lookahead == 4"));
    ctx.push_obligation(ProofObligation::assume("ca", "current_addr == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "prefetch_addr == current_addr + stride * lookahead",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1256", "prefetch_addr == 1256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "prefetch: 1000 + 64*4 = 1256");
}

#[test]
fn coherence_states_exclusive() {
    // MESI: only one cache can be in M or E state
    let mut ctx = VerificationContext::new();
    for v in &["cache_a_state", "cache_b_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("coherent", i32_ty());
    // 0=Invalid, 1=Shared, 2=Exclusive, 3=Modified
    ctx.push_obligation(ProofObligation::assume("cas", "cache_a_state == 3")); // Modified
    ctx.push_obligation(ProofObligation::assume("cbs", "cache_b_state == 0")); // Invalid
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "coherent == if cache_a_state >= 2 && cache_b_state == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "coherent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MESI: A=Modified, B=Invalid → coherent");
}
