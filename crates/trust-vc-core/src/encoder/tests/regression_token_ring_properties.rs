// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn token_passes_to_next_node() {
    let mut ctx = VerificationContext::new();
    for v in &["current_holder", "ring_size", "next_holder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "current_holder == 3"));
    ctx.push_obligation(ProofObligation::assume("rs", "ring_size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "next_holder == (current_holder + 1) % ring_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "next_holder == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "token pass: 3 → (3+1) % 8 = 4");
}

#[test]
fn token_wraps_around() {
    let mut ctx = VerificationContext::new();
    for v in &["current_holder", "ring_size", "next_holder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "current_holder == 7"));
    ctx.push_obligation(ProofObligation::assume("rs", "ring_size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "next_holder == (current_holder + 1) % ring_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "next_holder == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "token wrap: 7 → (7+1) % 8 = 0");
}

#[test]
fn exactly_one_token() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tokens_in_ring", u32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens_in_ring == 1"));
    ctx.push_obligation(ProofObligation::assert("one", "tokens_in_ring == 1"));
    ctx.push_obligation(ProofObligation::assert("positive", "tokens_in_ring > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "invariant: exactly 1 token in ring");
}

#[test]
fn maximum_wait_time() {
    // Worst case: wait for token to traverse entire ring
    let mut ctx = VerificationContext::new();
    for v in &["ring_size", "transfer_time", "max_wait"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rs", "ring_size == 10"));
    ctx.push_obligation(ProofObligation::assume("tt", "transfer_time == 5")); // ms per hop
    ctx.push_obligation(ProofObligation::assume(
        "mw_def",
        "max_wait == ring_size * transfer_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "max_wait == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "max wait: 10 nodes × 5ms = 50ms");
}

#[test]
fn token_holding_time_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["holding_time", "max_holding_time", "data_sent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("must_release", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ht", "holding_time == 10"));
    ctx.push_obligation(ProofObligation::assume("mht", "max_holding_time == 10"));
    ctx.push_obligation(ProofObligation::assume("ds", "data_sent == 1500")); // bytes sent during hold
    ctx.push_obligation(ProofObligation::assume(
        "mr_def",
        "must_release == if holding_time >= max_holding_time { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "must_release == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "token hold: 10 >= max 10 → must release");
}

#[test]
fn ring_latency_sum() {
    let mut ctx = VerificationContext::new();
    for v in &["hop_count", "latency_per_hop", "total_latency"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hc", "hop_count == 5"));
    ctx.push_obligation(ProofObligation::assume("lph", "latency_per_hop == 2")); // 2ms per hop
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_latency == hop_count * latency_per_hop",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total_latency == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ring latency: 5 hops × 2ms = 10ms");
}

#[test]
fn priority_token_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &["node_a_priority", "node_b_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_goes_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nap", "node_a_priority == 2")); // higher priority
    ctx.push_obligation(ProofObligation::assume("nbp", "node_b_priority == 5")); // lower priority
    ctx.push_obligation(ProofObligation::assume(
        "agf_def",
        "a_goes_first == if node_a_priority < node_b_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_goes_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "priority: node A (2) < node B (5) → A first");
}

#[test]
fn bandwidth_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["data_frames", "total_frames", "utilization_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("df", "data_frames == 80"));
    ctx.push_obligation(ProofObligation::assume("tf", "total_frames == 100")); // includes token frames
    ctx.push_obligation(ProofObligation::assume(
        "up_def",
        "utilization_pct == data_frames * 100 / total_frames",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "utilization_pct == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "utilization: 80/100 = 80%");
}

#[test]
fn node_removal_shrinks_ring() {
    let mut ctx = VerificationContext::new();
    for v in &["old_size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("os", "old_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_size == old_size - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "new_size == 9"));
    ctx.push_obligation(ProofObligation::assert("smaller", "new_size < old_size"));
    ctx.push_obligation(ProofObligation::assert("positive", "new_size > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove node: 10 → 9");
}

#[test]
fn duplicate_token_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("token_count", u32_ty());
    ctx.declare_var_typed("duplicate_detected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "token_count == 2")); // fault: 2 tokens
    ctx.push_obligation(ProofObligation::assume(
        "dd_def",
        "duplicate_detected == if token_count > 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duplicate_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duplicate: 2 tokens > 1 → detected");
}
