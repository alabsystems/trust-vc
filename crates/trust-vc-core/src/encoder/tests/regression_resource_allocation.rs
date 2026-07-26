// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn allocate_within_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "capacity", "request", "new_used"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 3"));
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume("request_val", "request == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "new_used_def",
        "new_used == used + request",
    ));
    ctx.push_obligation(ProofObligation::assert("fits", "new_used <= capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 + 2 = 5 <= 10 (fits in capacity)");
}

#[test]
fn reject_over_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "capacity", "request"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_alloc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 8"));
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume("request_val", "request == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "can_alloc_def",
        "can_alloc == if used + request <= capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "can_alloc == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8 + 5 = 13 > 10 (over capacity)");
}

#[test]
fn release_frees_space() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "released", "new_used"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 7"));
    ctx.push_obligation(ProofObligation::assume("released_val", "released == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "new_used_def",
        "new_used == used - released",
    ));
    ctx.push_obligation(ProofObligation::assert("freed", "new_used == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "release 3 of 7 used = 4 remaining");
}

#[test]
fn allocate_release_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "after_alloc", "after_release"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "after_alloc_def",
        "after_alloc == used + 3",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "after_release_def",
        "after_release == after_alloc - 3",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "after_release == used"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "allocate then release same amount = identity");
}

#[test]
fn remaining_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "capacity", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 6"));
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "remaining_def",
        "remaining == capacity - used",
    ));
    ctx.push_obligation(ProofObligation::assert("four_left", "remaining == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 - 6 = 4 remaining");
}

#[test]
fn full_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 10"));
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assert("full", "used == capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resource fully utilized");
}

#[test]
fn split_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["total", "a_share", "b_share"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("total_val", "total == 10"));
    ctx.push_obligation(ProofObligation::assume("a_share_val", "a_share == 6"));
    ctx.push_obligation(ProofObligation::assume("b_share_val", "b_share == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "sum_is_total",
        "a_share + b_share == total",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "6 + 4 = 10 (shares sum to total)");
}

#[test]
fn watermark_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "watermark", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("used_val", "used == 7"));
    ctx.push_obligation(ProofObligation::assume("watermark_val", "watermark == 8"));
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "ok == if used <= watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("below_watermark", "ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 <= 8 (below watermark)");
}

#[test]
fn reservation_double_free_guard() {
    let mut ctx = VerificationContext::new();
    for v in &["slots", "after_free1", "after_free2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("slots_val", "slots == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "after_free1_def",
        "after_free1 == slots + 1",
    ));
    // Guard: only free if was actually allocated (tracked by count)
    ctx.push_obligation(ProofObligation::assume(
        "after_free2_def",
        "after_free2 == if after_free1 > slots { after_free1 } else { after_free1 + 1 }",
    ));
    // Second free is blocked because after_free1 > slots
    ctx.push_obligation(ProofObligation::assert(
        "no_double_free",
        "after_free2 == 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double free guard prevents second free");
}

#[test]
fn proportional_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["total", "share_a", "share_b", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= 0 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("total_val", "total == 100"));
    // 60/40 split
    ctx.push_obligation(ProofObligation::assume("share_a_def", "share_a == 60"));
    ctx.push_obligation(ProofObligation::assume("share_b_def", "share_b == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "sum_def",
        "sum == share_a + share_b",
    ));
    ctx.push_obligation(ProofObligation::assert("conserved", "sum == total"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "60 + 40 = 100 (allocation conserved)");
}
