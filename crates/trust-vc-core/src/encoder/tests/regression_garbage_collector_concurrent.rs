// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn safe_point_all_threads_paused() {
    let mut ctx = VerificationContext::new();
    for v in &["total_threads", "paused_threads"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_safe_point", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tt", "total_threads == 8"));
    ctx.push_obligation(ProofObligation::assume("pt", "paused_threads == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "asp_def",
        "at_safe_point == if paused_threads == total_threads { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("safe", "at_safe_point == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "safe point: 8/8 threads paused");
}

#[test]
fn read_barrier_snapshot_at_mark_start() {
    let mut ctx = VerificationContext::new();
    for v in &["heap_version_at_mark", "read_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hv", "heap_version_at_mark == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "read_version == heap_version_at_mark",
    ));
    ctx.push_obligation(ProofObligation::assert("consistent", "read_version == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "read barrier: snapshot at mark start version 42");
}

#[test]
fn concurrent_mark_progress() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "marked_before",
        "marked_this_step",
        "marked_after",
        "total_reachable",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mb", "marked_before == 500"));
    ctx.push_obligation(ProofObligation::assume("mts", "marked_this_step == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ma_def",
        "marked_after == marked_before + marked_this_step",
    ));
    ctx.push_obligation(ProofObligation::assume("tr", "total_reachable == 1000"));
    ctx.push_obligation(ProofObligation::assert("is_600", "marked_after == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "not_done",
        "marked_after < total_reachable",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concurrent mark: 500+100=600, 400 remaining");
}

#[test]
fn satb_snapshot_write_barrier() {
    // SATB (Snapshot At The Beginning): log old value before overwrite
    let mut ctx = VerificationContext::new();
    for v in &["old_ref", "new_ref", "logged_ref"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("or", "old_ref == 100"));
    ctx.push_obligation(ProofObligation::assume("nr", "new_ref == 200"));
    ctx.push_obligation(ProofObligation::assume("lr_def", "logged_ref == old_ref")); // log before overwrite
    ctx.push_obligation(ProofObligation::assert("saved", "logged_ref == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATB: logged old ref 100 before overwrite to 200");
}

#[test]
fn gc_pause_time_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_time", "fixup_time", "total_pause", "max_pause"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_target", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "scan_time == 5")); // ms
    ctx.push_obligation(ProofObligation::assume("ft", "fixup_time == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_pause == scan_time + fixup_time",
    ));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pause == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "wt_def",
        "within_target == if total_pause <= max_pause { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_target == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pause: 5+3=8ms <= 10ms target");
}

#[test]
fn remembered_set_cross_region() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "region_a_refs_to_b",
        "region_b_refs_to_a",
        "total_cross_refs",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ab", "region_a_refs_to_b == 15"));
    ctx.push_obligation(ProofObligation::assume("ba", "region_b_refs_to_a == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "tcr_def",
        "total_cross_refs == region_a_refs_to_b + region_b_refs_to_a",
    ));
    ctx.push_obligation(ProofObligation::assert("is_23", "total_cross_refs == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remembered set: 15+8 = 23 cross-region refs");
}

#[test]
fn evacuation_copies_live() {
    let mut ctx = VerificationContext::new();
    for v in &["region_objects", "live_objects", "evacuated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ro", "region_objects == 500"));
    ctx.push_obligation(ProofObligation::assume("lo", "live_objects == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "evacuated == live_objects",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "evacuated == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "evacuated < region_objects",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evacuate: 200 live of 500 total");
}

#[test]
fn reference_update_after_move() {
    let mut ctx = VerificationContext::new();
    for v in &["old_address", "new_address", "forwarding_pointer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oa", "old_address == 1000"));
    ctx.push_obligation(ProofObligation::assume("na", "new_address == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "forwarding_pointer == new_address",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "redirects",
        "forwarding_pointer == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moved",
        "forwarding_pointer != old_address",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forwarding: 1000 → 5000");
}

#[test]
fn region_selection_by_garbage_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "region_a_garbage",
        "region_b_garbage",
        "region_a_total",
        "region_b_total",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("collect_a_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rag", "region_a_garbage == 400"));
    ctx.push_obligation(ProofObligation::assume("rat", "region_a_total == 500"));
    ctx.push_obligation(ProofObligation::assume("rbg", "region_b_garbage == 100"));
    ctx.push_obligation(ProofObligation::assume("rbt", "region_b_total == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "collect_a_first == if region_a_garbage > region_b_garbage { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("a_first", "collect_a_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "region A (400 garbage) > B (100) → collect A first",
    );
}

#[test]
fn concurrent_sweep_reclaim_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["regions_total", "regions_swept", "regions_remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rt", "regions_total == 100"));
    ctx.push_obligation(ProofObligation::assume("rs", "regions_swept == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "rr_def",
        "regions_remaining == regions_total - regions_swept",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "regions_remaining == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concurrent sweep: 100-60 = 40 regions remaining");
}
