// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mark_reachable_object() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("obj_addr", u32_ty());
    ctx.declare_var_typed("reachable", i32_ty());
    ctx.declare_var_typed("marked", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oa", "obj_addr == 1000"));
    ctx.push_obligation(ProofObligation::assume("r", "reachable == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "marked == if reachable == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_marked", "marked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reachable object gets marked");
}

#[test]
fn sweep_unmarked_object() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("marked", i32_ty());
    ctx.declare_var_typed("freed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "marked == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "freed == if marked == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_freed", "freed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unmarked object gets freed");
}

#[test]
fn live_objects_after_gc() {
    // After GC: live = total - garbage
    let mut ctx = VerificationContext::new();
    for v in &["total", "garbage", "live"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "total == 100"));
    ctx.push_obligation(ProofObligation::assume("g", "garbage == 30"));
    ctx.push_obligation(ProofObligation::assume("l_def", "live == total - garbage"));
    ctx.push_obligation(ProofObligation::assert("is_70", "live == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 total - 30 garbage = 70 live");
}

#[test]
fn generational_young_to_old() {
    // Object survives N collections → promote to old generation
    let mut ctx = VerificationContext::new();
    for v in &["survive_count", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("promote", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sc", "survive_count == 5"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "promote == if survive_count >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("promoted", "promote == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "survived 5 >= threshold 3 → promote");
}

#[test]
fn heap_occupancy_ratio() {
    // GC triggers when occupancy > threshold
    let mut ctx = VerificationContext::new();
    for v in &["used", "capacity", "occupancy_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("u", "used == 80"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "op_def",
        "occupancy_pct == used * 100 / capacity",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "occupancy_pct == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "80/100 = 80% occupancy");
}

#[test]
fn root_set_includes_stack() {
    let mut ctx = VerificationContext::new();
    for v in &["stack_refs", "global_refs", "total_roots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sr", "stack_refs == 10"));
    ctx.push_obligation(ProofObligation::assume("gr", "global_refs == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "total_roots == stack_refs + global_refs",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "total_roots == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "root set: 10 stack + 5 global = 15");
}

#[test]
fn compaction_preserves_live_count() {
    let mut ctx = VerificationContext::new();
    for v in &["live_before", "live_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "live_before == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "live_after == live_before",
    ));
    ctx.push_obligation(ProofObligation::assert("preserved", "live_after == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compaction preserves 42 live objects");
}

#[test]
fn write_barrier_dirty_card() {
    let mut ctx = VerificationContext::new();
    for v in &["write_addr", "card_size", "card_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("card_dirty", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wa", "write_addr == 4096"));
    ctx.push_obligation(ProofObligation::assume("cs", "card_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "ci_def",
        "card_index == write_addr / card_size",
    ));
    ctx.push_obligation(ProofObligation::assume("cd_def", "card_dirty == 1")); // barrier marks dirty
    ctx.push_obligation(ProofObligation::assert("dirty", "card_dirty == 1"));
    ctx.push_obligation(ProofObligation::assert("card_8", "card_index == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "write to 4096 dirties card 8");
}

#[test]
fn free_list_size_after_sweep() {
    let mut ctx = VerificationContext::new();
    for v in &["free_before", "swept", "free_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fb", "free_before == 20"));
    ctx.push_obligation(ProofObligation::assume("s", "swept == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "free_after == free_before + swept",
    ));
    ctx.push_obligation(ProofObligation::assert("is_35", "free_after == 35"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free list: 20 + 15 swept = 35");
}

#[test]
fn concurrent_gc_safe_point() {
    // Thread must reach safe point before GC can proceed
    let mut ctx = VerificationContext::new();
    for v in &["thread_count", "safe_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("all_safe", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "thread_count == 8"));
    ctx.push_obligation(ProofObligation::assume("sc", "safe_count == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "all_safe == if safe_count == thread_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("safe", "all_safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "all 8 threads at safe point");
}
