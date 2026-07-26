// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cache_hit_returns_cached() {
    let mut ctx = VerificationContext::new();
    for v in &["cached_value", "returned"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_cache", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cv", "cached_value == 42"));
    ctx.push_obligation(ProofObligation::assume("ic", "in_cache == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "returned == if in_cache == 1 { cached_value } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_42", "returned == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache hit → return cached value 42");
}

#[test]
fn cache_miss_triggers_fetch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("in_cache", i32_ty());
    ctx.declare_var_typed("needs_fetch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ic", "in_cache == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "needs_fetch == if in_cache == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fetch", "needs_fetch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cache miss → needs fetch");
}

#[test]
fn ttl_expiry_invalidates() {
    let mut ctx = VerificationContext::new();
    for v in &["entry_time", "ttl", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("et", "entry_time == 100"));
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 60"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if current_time < entry_time + ttl { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("expired", "valid == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 200 >= entry 100 + TTL 60 → expired");
}

#[test]
fn write_through_updates_both() {
    let mut ctx = VerificationContext::new();
    for v in &["new_val", "cache_val", "storage_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nv", "new_val == 99"));
    ctx.push_obligation(ProofObligation::assume("cv_def", "cache_val == new_val")); // write-through
    ctx.push_obligation(ProofObligation::assume("sv_def", "storage_val == new_val"));
    ctx.push_obligation(ProofObligation::assert("cache_eq", "cache_val == 99"));
    ctx.push_obligation(ProofObligation::assert("storage_eq", "storage_val == 99"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write-through: cache and storage both 99");
}

#[test]
fn eviction_makes_room() {
    let mut ctx = VerificationContext::new();
    for v in &["entries", "capacity", "after_evict"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("e", "entries == 100"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ae_def",
        "after_evict == entries - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("room", "after_evict < capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evict one: 99 < capacity 100");
}

#[test]
fn cache_size_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("e", "entries == 50"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 100"));
    ctx.push_obligation(ProofObligation::assert("bounded", "entries <= max_entries"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "50 entries <= 100 max");
}

#[test]
fn multi_tier_cache_check_order() {
    // L1 → L2 → L3 → storage
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("l1_hit", i32_ty());
    ctx.declare_var_typed("l2_hit", i32_ty());
    ctx.declare_var_typed("check_l2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("l1", "l1_hit == 0")); // miss
    ctx.push_obligation(ProofObligation::assume(
        "cl2_def",
        "check_l2 == if l1_hit == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("falls_through", "check_l2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "L1 miss → check L2");
}

#[test]
fn invalidation_removes_entry() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "entries_after == entries_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_49", "entries_after == 49"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "invalidate one: 50 → 49 entries");
}

#[test]
fn prefetch_adds_entry() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "entries_after == entries_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_31", "entries_after == 31"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefetch adds one: 30 → 31 entries");
}

#[test]
fn stale_while_revalidate() {
    let mut ctx = VerificationContext::new();
    for v in &["entry_time", "ttl", "stale_window", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("serve_stale", i32_ty());
    ctx.push_obligation(ProofObligation::assume("et", "entry_time == 100"));
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 60"));
    ctx.push_obligation(ProofObligation::assume("sw", "stale_window == 30"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 175"));
    ctx.push_obligation(ProofObligation::assume(
        "ss_def",
        "serve_stale == if current_time >= entry_time + ttl && current_time < entry_time + ttl + stale_window { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stale_ok", "serve_stale == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 175 in stale window [160, 190) → serve stale");
}
