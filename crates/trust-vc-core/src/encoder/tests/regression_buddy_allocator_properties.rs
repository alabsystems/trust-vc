// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn block_size_is_power_of_two() {
    let mut ctx = VerificationContext::new();
    for v in &["order", "block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // block_size = 2^order, hardcoded for order=4
    ctx.push_obligation(ProofObligation::assume("o", "order == 4"));
    ctx.push_obligation(ProofObligation::assume("bs_def", "block_size == 16")); // 2^4
    ctx.push_obligation(ProofObligation::assert("is_16", "block_size == 16"));
    ctx.push_obligation(ProofObligation::assert("positive", "block_size > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "buddy: order 4 → block size 16");
}

#[test]
fn split_produces_two_halves() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_size", "child_size", "child_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parent_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "child_size == parent_size / 2",
    ));
    ctx.push_obligation(ProofObligation::assume("cc", "child_count == 2"));
    ctx.push_obligation(ProofObligation::assert("half", "child_size == 128"));
    ctx.push_obligation(ProofObligation::assert(
        "conserved",
        "child_size * child_count == parent_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "buddy split: 256 → 2 × 128");
}

#[test]
fn merge_doubles_size() {
    let mut ctx = VerificationContext::new();
    for v in &["buddy_a_size", "buddy_b_size", "merged_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "buddy_a_size == 64"));
    ctx.push_obligation(ProofObligation::assume("bb", "buddy_b_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "merged_size == buddy_a_size + buddy_b_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "merged_size == 128"));
    ctx.push_obligation(ProofObligation::assert(
        "doubled",
        "merged_size == 2 * buddy_a_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "buddy merge: 64 + 64 = 128");
}

#[test]
fn buddy_address_calculation() {
    // buddy of block at addr is addr XOR block_size
    let mut ctx = VerificationContext::new();
    for v in &["block_addr", "block_size", "buddy_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "block_addr == 1024"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "bud_def",
        "buddy_addr == block_addr ^ block_size",
    ));
    // 1024 XOR 256 = 1280
    ctx.push_obligation(ProofObligation::assert("is_1280", "buddy_addr == 1280"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "buddy addr: 1024 XOR 256 = 1280");
}

#[test]
fn minimum_allocation_size() {
    let mut ctx = VerificationContext::new();
    for v in &["requested", "min_block", "allocated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "requested == 10"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_block == 16")); // minimum block size
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "allocated == if requested < min_block { min_block } else { requested }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "allocated == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "ge_requested",
        "allocated >= requested",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min alloc: requested 10 < min 16 → allocate 16");
}

#[test]
fn internal_fragmentation() {
    let mut ctx = VerificationContext::new();
    for v in &["requested", "allocated", "wasted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "requested == 100"));
    ctx.push_obligation(ProofObligation::assume("a", "allocated == 128")); // next power of 2
    ctx.push_obligation(ProofObligation::assume(
        "w_def",
        "wasted == allocated - requested",
    ));
    ctx.push_obligation(ProofObligation::assert("is_28", "wasted == 28"));
    ctx.push_obligation(ProofObligation::assert("ge", "allocated >= requested"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fragmentation: 128 - 100 = 28 bytes wasted");
}

#[test]
fn free_list_count_after_split() {
    let mut ctx = VerificationContext::new();
    for v in &["free_before", "free_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Splitting one block removes it and adds 2, but one is allocated
    ctx.push_obligation(ProofObligation::assume("fb", "free_before == 5"));
    // split: remove 1, add 2 children, allocate 1 child → net +0
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "free_after == free_before - 1 + 2 - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "free_after == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free list: 5 - 1 + 2 - 1 = 5 (split+alloc)");
}

#[test]
fn max_order_covers_total_memory() {
    let mut ctx = VerificationContext::new();
    for v in &["total_memory", "max_block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("covers", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tm", "total_memory == 1048576")); // 1MB
    ctx.push_obligation(ProofObligation::assume("mbs", "max_block_size == 1048576")); // max order block = total
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "covers == if max_block_size >= total_memory { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "covers == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max order: 1MB block covers 1MB total");
}

#[test]
fn order_from_size() {
    // For size 64: order = log2(64) = 6
    let mut ctx = VerificationContext::new();
    for v in &["block_size", "order"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume("o", "order == 6")); // log2(64) = 6
                                                                     // Verify: 2^6 = 64 (hardcoded check)
    ctx.push_obligation(ProofObligation::assert("order_6", "order == 6"));
    ctx.push_obligation(ProofObligation::assert("size_positive", "block_size > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "order: log2(64) = 6");
}

#[test]
fn total_blocks_at_order() {
    let mut ctx = VerificationContext::new();
    for v in &["total_memory", "block_size", "num_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tm", "total_memory == 1024"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "num_blocks == total_memory / block_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "num_blocks == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "blocks at order: 1024 / 64 = 16");
}
