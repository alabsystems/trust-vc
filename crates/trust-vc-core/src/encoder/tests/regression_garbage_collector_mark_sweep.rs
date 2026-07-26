// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mark_phase_visits_all_reachable() {
    let mut ctx = VerificationContext::new();
    for v in &["total_objects", "reachable", "marked"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("to", "total_objects == 1000"));
    ctx.push_obligation(ProofObligation::assume("r", "reachable == 600"));
    ctx.push_obligation(ProofObligation::assume("m_def", "marked == reachable"));
    ctx.push_obligation(ProofObligation::assert("all_marked", "marked == 600"));
    ctx.push_obligation(ProofObligation::assert("subset", "marked <= total_objects"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mark: 600 reachable objects marked out of 1000");
}

#[test]
fn sweep_reclaims_unmarked() {
    let mut ctx = VerificationContext::new();
    for v in &["total_objects", "marked", "reclaimed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("to", "total_objects == 1000"));
    ctx.push_obligation(ProofObligation::assume("m", "marked == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "reclaimed == total_objects - marked",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "reclaimed == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sweep: 1000 - 600 marked = 400 reclaimed");
}

#[test]
fn tri_color_white_to_gray() {
    // White (unvisited) → Gray (discovered but children not scanned)
    let mut ctx = VerificationContext::new();
    for v in &["white_count", "gray_count", "discovered"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wc", "white_count == 100"));
    ctx.push_obligation(ProofObligation::assume("gc", "gray_count == 0"));
    ctx.push_obligation(ProofObligation::assume("d", "discovered == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "white_dec",
        "white_count - discovered == 90",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gray_inc",
        "gray_count + discovered == 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tri-color: 10 white → gray");
}

#[test]
fn gray_to_black_after_scan() {
    // Gray → Black (all children scanned)
    let mut ctx = VerificationContext::new();
    for v in &["gray_before", "scanned", "gray_after", "black_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("gb", "gray_before == 10"));
    ctx.push_obligation(ProofObligation::assume("s", "scanned == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ga_def",
        "gray_after == gray_before - scanned",
    ));
    ctx.push_obligation(ProofObligation::assume("ba_def", "black_after == scanned"));
    ctx.push_obligation(ProofObligation::assert("gray_dec", "gray_after == 7"));
    ctx.push_obligation(ProofObligation::assert("black_inc", "black_after == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan: 3 gray → black, 7 gray remaining");
}

#[test]
fn gc_preserves_live_objects() {
    let mut ctx = VerificationContext::new();
    for v in &["live_before", "live_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "live_before == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "live_after == live_before",
    )); // GC doesn't touch live
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "live_after == live_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC preserves all 600 live objects");
}

#[test]
fn heap_usage_after_gc() {
    let mut ctx = VerificationContext::new();
    for v in &["used_before", "reclaimed", "used_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ub", "used_before == 800"));
    ctx.push_obligation(ProofObligation::assume("r", "reclaimed == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "ua_def",
        "used_after == used_before - reclaimed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "used_after == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heap after GC: 800 - 300 = 500");
}

#[test]
fn generational_nursery_promotion() {
    let mut ctx = VerificationContext::new();
    for v in &["nursery_objects", "survived_gc", "promoted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("no", "nursery_objects == 1000"));
    ctx.push_obligation(ProofObligation::assume("sg", "survived_gc == 100")); // 10% survive
    ctx.push_obligation(ProofObligation::assume("p_def", "promoted == survived_gc"));
    ctx.push_obligation(ProofObligation::assert("is_100", "promoted == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "promoted < nursery_objects",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nursery: 100 of 1000 promoted to old gen");
}

#[test]
fn write_barrier_tracks_references() {
    let mut ctx = VerificationContext::new();
    for v in &["card_table_entries", "new_reference", "total_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cte", "card_table_entries == 50"));
    ctx.push_obligation(ProofObligation::assume("nr", "new_reference == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_entries == card_table_entries + new_reference",
    ));
    ctx.push_obligation(ProofObligation::assert("is_51", "total_entries == 51"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write barrier: 50 + 1 = 51 card entries");
}

#[test]
fn free_list_after_sweep() {
    let mut ctx = VerificationContext::new();
    for v in &["free_list_before", "newly_freed", "free_list_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flb", "free_list_before == 200"));
    ctx.push_obligation(ProofObligation::assume("nf", "newly_freed == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "fla_def",
        "free_list_after == free_list_before + newly_freed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_600", "free_list_after == 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free list: 200 + 400 swept = 600");
}

#[test]
fn gc_cycle_total_invariant() {
    // Total = live + garbage = constant before/after GC
    let mut ctx = VerificationContext::new();
    for v in &["live", "garbage", "total_before", "total_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "live == 600"));
    ctx.push_obligation(ProofObligation::assume("g", "garbage == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_before == live + garbage",
    ));
    ctx.push_obligation(ProofObligation::assume("ta_def", "total_after == live")); // garbage reclaimed
    ctx.push_obligation(ProofObligation::assert(
        "before_1000",
        "total_before == 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("after_600", "total_after == 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: 600+400=1000 → 600 live after sweep");
}
