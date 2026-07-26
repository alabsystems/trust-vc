// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn get_promotes_to_front() {
    // Accessing element moves it to front (most recently used)
    let mut ctx = VerificationContext::new();
    for v in &["elem_pos_before", "elem_pos_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("before", "elem_pos_before == 5"));
    ctx.push_obligation(ProofObligation::assume("after_def", "elem_pos_after == 0")); // front
    ctx.push_obligation(ProofObligation::assert("at_front", "elem_pos_after == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU get: promoted to front");
}

#[test]
fn eviction_removes_tail() {
    // LRU evicts from tail (least recently used)
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 10"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    // Insert requires eviction: size stays at capacity
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == capacity"));
    ctx.push_obligation(ProofObligation::assert("at_capacity", "new_size == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU: evict keeps size at capacity");
}

#[test]
fn insert_under_capacity_grows() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_size == if size < capacity { size + 1 } else { size }",
    ));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU insert under capacity: 5 → 6");
}

#[test]
fn capacity_invariant() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 8"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assert("bounded", "size <= capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU: size 8 <= capacity 10");
}

#[test]
fn hit_increments_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["hits", "new_hits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hits == 50"));
    ctx.push_obligation(ProofObligation::assume("nh_def", "new_hits == hits + 1"));
    ctx.push_obligation(ProofObligation::assert("is_51", "new_hits == 51"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache hit: 50 → 51");
}

#[test]
fn miss_increments_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["misses", "new_misses"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("m", "misses == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "nm_def",
        "new_misses == misses + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_21", "new_misses == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache miss: 20 → 21");
}

#[test]
fn hit_rate_calculation() {
    // hit_rate = hits * 100 / (hits + misses)
    let mut ctx = VerificationContext::new();
    for v in &["hits", "misses", "total", "hit_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hits == 80"));
    ctx.push_obligation(ProofObligation::assume("m", "misses == 20"));
    ctx.push_obligation(ProofObligation::assume("t_def", "total == hits + misses"));
    ctx.push_obligation(ProofObligation::assume(
        "hr_def",
        "hit_rate == hits * 100 / total",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "hit_rate == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hit rate: 80/100 = 80%");
}

#[test]
fn clear_empties_cache() {
    let mut ctx = VerificationContext::new();
    for v in &["size_before", "size_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "size_before == 8"));
    ctx.push_obligation(ProofObligation::assume("sa_def", "size_after == 0"));
    ctx.push_obligation(ProofObligation::assert("empty", "size_after == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU clear: size → 0");
}

#[test]
fn duplicate_insert_no_growth() {
    // Inserting existing key doesn't increase size
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 5"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size")); // duplicate
    ctx.push_obligation(ProofObligation::assert("same", "new_size == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duplicate insert: size unchanged");
}

#[test]
fn resize_doubles_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["old_cap", "new_cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_cap == 16"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_cap == old_cap * 2"));
    ctx.push_obligation(ProofObligation::assert("is_32", "new_cap == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "LRU resize: 16 → 32");
}
