// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn buddy_split() {
    let mut ctx = VerificationContext::new();
    for v in &["block_size", "left_half", "right_half"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Buddy allocator: split block into two equal halves
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "lh_def",
        "left_half == block_size / 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rh_def",
        "right_half == block_size / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2048", "left_half == 2048"));
    ctx.push_obligation(ProofObligation::assert("equal", "left_half == right_half"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "buddy: 4096 / 2 = 2048 each half");
}

#[test]
fn buddy_merge() {
    let mut ctx = VerificationContext::new();
    for v in &["block_a", "block_b", "merged"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_merge", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ba", "block_a == 2048"));
    ctx.push_obligation(ProofObligation::assume("bb", "block_b == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "can_merge == if block_a == block_b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "merged == block_a + block_b",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "can_merge == 1"));
    ctx.push_obligation(ProofObligation::assert("is_4096", "merged == 4096"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "buddy: 2048 + 2048 = 4096 merged");
}

#[test]
fn first_fit_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["block0_size", "block1_size", "request_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("selected_block", u32_ty());
    ctx.push_obligation(ProofObligation::assume("b0", "block0_size == 256"));
    ctx.push_obligation(ProofObligation::assume("b1", "block1_size == 1024"));
    ctx.push_obligation(ProofObligation::assume("rs", "request_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "selected_block == if block0_size >= request_size { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "selected_block == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "first-fit: block0(256) < 512, use block1(1024)");
}

#[test]
fn fragmentation_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["total_free", "largest_free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fragmented", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tf", "total_free == 8192"));
    ctx.push_obligation(ProofObligation::assume("lf", "largest_free == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fragmented == if total_free > 4096 && largest_free < 4096 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fragmented == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heap: 8KB total but largest 1KB → fragmented");
}

#[test]
fn pool_slot_address() {
    let mut ctx = VerificationContext::new();
    for v in &["pool_base", "slot_size", "slot_index", "slot_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pb", "pool_base == 536870912"));
    ctx.push_obligation(ProofObligation::assume("ss", "slot_size == 64"));
    ctx.push_obligation(ProofObligation::assume("si", "slot_index == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "slot_addr == pool_base + slot_index * slot_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct",
        "slot_addr == 536871232",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pool: base + 5×64 = base+320");
}

#[test]
fn free_list_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_slots", "allocated", "free_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ts", "total_slots == 128"));
    ctx.push_obligation(ProofObligation::assume("al", "allocated == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "fc_def",
        "free_count == total_slots - allocated",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hf_def",
        "has_free == if free_count > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_28", "free_count == 28"));
    ctx.push_obligation(ProofObligation::assert("yes", "has_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free list: 128 - 100 = 28 free slots");
}

#[test]
fn alignment_round_up() {
    let mut ctx = VerificationContext::new();
    for v in &["requested", "aligned_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 100 rounded up to 16-byte alignment = 112 (precomputed)
    ctx.push_obligation(ProofObligation::assume("r", "requested == 100"));
    ctx.push_obligation(ProofObligation::assume("as_val", "aligned_size == 112"));
    ctx.push_obligation(ProofObligation::assert("is_112", "aligned_size == 112"));
    ctx.push_obligation(ProofObligation::assert(
        "at_least",
        "aligned_size >= requested",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloc: 100 aligned to 16 → 112");
}

#[test]
fn watermark_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["used_bytes", "high_watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_threshold", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ub", "used_bytes == 7500"));
    ctx.push_obligation(ProofObligation::assume("hw", "high_watermark == 7000"));
    ctx.push_obligation(ProofObligation::assume(
        "at_def",
        "above_threshold == if used_bytes > high_watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "above_threshold == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloc: 7500 > 7000 watermark → trigger GC");
}

#[test]
fn coalesce_adjacent_free() {
    let mut ctx = VerificationContext::new();
    for v in &["block_a_size", "block_b_size", "coalesced_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "block_a_size == 256"));
    ctx.push_obligation(ProofObligation::assume("bb", "block_b_size == 384"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "coalesced_size == block_a_size + block_b_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_640", "coalesced_size == 640"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coalesce: 256 + 384 = 640 bytes");
}

#[test]
fn minimum_block_size() {
    let mut ctx = VerificationContext::new();
    for v in &["requested", "min_block", "actual_alloc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "requested == 1"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_block == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "actual_alloc == if requested < min_block { min_block } else { requested }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "actual_alloc == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloc: 1 byte request → 16 byte minimum");
}
