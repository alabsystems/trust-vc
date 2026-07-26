// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cache_hit_no_eviction() {
    let mut ctx = VerificationContext::new();
    for v in &["size_before", "size_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "size_before == 3"));
    // Hit: size unchanged
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "size_after == size_before",
    ));
    ctx.push_obligation(ProofObligation::assert("unchanged", "size_after == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache hit preserves size");
}

#[test]
fn cache_miss_below_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 3"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "new_def",
        "new_size == if size < capacity { size + 1 } else { size }",
    ));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "miss below capacity: size 3 → 4");
}

#[test]
fn cache_miss_at_capacity_evicts() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 5"));
    // Evict one, add one: size unchanged
    ctx.push_obligation(ProofObligation::assume(
        "new_def",
        "new_size == if size < capacity { size + 1 } else { size }",
    ));
    ctx.push_obligation(ProofObligation::assert("same_size", "new_size == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "miss at capacity: evict + insert, size stays");
}

#[test]
fn lru_evicts_oldest() {
    // LRU: track access time, evict smallest timestamp
    let mut ctx = VerificationContext::new();
    for v in &["t_a", "t_b", "t_c", "evicted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ta", "t_a == 10"));
    ctx.push_obligation(ProofObligation::assume("tb", "t_b == 5"));
    ctx.push_obligation(ProofObligation::assume("tc", "t_c == 15"));
    // Evict the one with smallest timestamp (b at time 5)
    ctx.push_obligation(ProofObligation::assume(
        "evict_def",
        "evicted == if t_a <= t_b && t_a <= t_c { 0 } else { if t_b <= t_c { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("evict_b", "evicted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU evicts entry with oldest access time");
}

#[test]
fn fifo_evicts_first_inserted() {
    let mut ctx = VerificationContext::new();
    for v in &["insert_a", "insert_b", "insert_c", "evicted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ia", "insert_a == 1"));
    ctx.push_obligation(ProofObligation::assume("ib", "insert_b == 2"));
    ctx.push_obligation(ProofObligation::assume("ic", "insert_c == 3"));
    // FIFO: evict smallest insert order
    ctx.push_obligation(ProofObligation::assume(
        "evict_def",
        "evicted == if insert_a <= insert_b && insert_a <= insert_c { 0 } else { if insert_b <= insert_c { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("evict_a", "evicted == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO evicts first inserted entry");
}

#[test]
fn access_updates_timestamp() {
    let mut ctx = VerificationContext::new();
    for v in &["old_time", "clock", "new_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("old", "old_time == 5"));
    ctx.push_obligation(ProofObligation::assume("clk", "clock == 20"));
    ctx.push_obligation(ProofObligation::assume("new_def", "new_time == clock"));
    ctx.push_obligation(ProofObligation::assert("updated", "new_time > old_time"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "access updates timestamp to current clock");
}

#[test]
fn hit_rate_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["hits", "misses", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hits == 7"));
    ctx.push_obligation(ProofObligation::assume("m", "misses == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == hits + misses",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total = hits + misses = 10");
}

#[test]
fn capacity_invariant_after_operations() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 5"));
    ctx.push_obligation(ProofObligation::assert("bounded", "size <= capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "size <= capacity invariant holds");
}

#[test]
fn eviction_priority_comparison() {
    // Compare two entries by priority (lower = evict first)
    let mut ctx = VerificationContext::new();
    for v in &["priority_a", "priority_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("evict_a_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pa", "priority_a == 3"));
    ctx.push_obligation(ProofObligation::assume("pb", "priority_b == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "evict_def",
        "evict_a_first == if priority_a < priority_b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("a_first", "evict_a_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lower priority evicted first: 3 < 7");
}

#[test]
fn two_way_set_associative() {
    // 2-way: each set has 2 slots, check which to evict
    let mut ctx = VerificationContext::new();
    for v in &["slot0_time", "slot1_time", "evict_slot"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0t", "slot0_time == 10"));
    ctx.push_obligation(ProofObligation::assume("s1t", "slot1_time == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "evict_def",
        "evict_slot == if slot0_time <= slot1_time { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("evict_0", "evict_slot == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2-way associative: evict older slot");
}
