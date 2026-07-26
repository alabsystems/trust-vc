// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn min_heap_parent_leq_child() {
    let mut ctx = VerificationContext::new();
    for v in &["parent", "left_child", "right_child"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "parent == 5"));
    ctx.push_obligation(ProofObligation::assume("lc", "left_child == 10"));
    ctx.push_obligation(ProofObligation::assume("rc", "right_child == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "heap_prop",
        "parent <= left_child && parent <= right_child",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min-heap: 5 <= 10, 5 <= 8");
}

#[test]
fn max_heap_parent_geq_child() {
    let mut ctx = VerificationContext::new();
    for v in &["parent", "left_child", "right_child"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "parent == 50"));
    ctx.push_obligation(ProofObligation::assume("lc", "left_child == 30"));
    ctx.push_obligation(ProofObligation::assume("rc", "right_child == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "heap_prop",
        "parent >= left_child && parent >= right_child",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max-heap: 50 >= 30, 50 >= 40");
}

#[test]
fn insert_increases_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size_before", "size_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "size_before == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "size_after == size_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("grows", "size_after == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heap insert: 15 → 16");
}

#[test]
fn extract_min_returns_smallest() {
    let mut ctx = VerificationContext::new();
    for v in &["extracted", "remaining_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("e", "extracted == 3"));
    ctx.push_obligation(ProofObligation::assume("rm", "remaining_min == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "smallest",
        "extracted <= remaining_min",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "extract min: 3 <= remaining min 7");
}

#[test]
fn left_child_index() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_idx", "left_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pi", "parent_idx == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "li_def",
        "left_idx == 2 * parent_idx + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "left_idx == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "left child of 3 = 2*3+1 = 7");
}

#[test]
fn right_child_index() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_idx", "right_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pi", "parent_idx == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ri_def",
        "right_idx == 2 * parent_idx + 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "right_idx == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "right child of 3 = 2*3+2 = 8");
}

#[test]
fn parent_index() {
    let mut ctx = VerificationContext::new();
    for v in &["child_idx", "parent_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ci", "child_idx == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "pi_def",
        "parent_idx == (child_idx - 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "parent_idx == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "parent of 7 = (7-1)/2 = 3");
}

#[test]
fn heapify_up_swaps_when_violated() {
    let mut ctx = VerificationContext::new();
    for v in &["child_val", "parent_val", "new_child", "new_parent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cv", "child_val == 2")); // smaller than parent
    ctx.push_obligation(ProofObligation::assume("pv", "parent_val == 10"));
    // swap
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_child == parent_val"));
    ctx.push_obligation(ProofObligation::assume("np_def", "new_parent == child_val"));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "new_parent <= new_child",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heapify up: swap 2↔10 restores order");
}

#[test]
fn heap_size_after_build() {
    let mut ctx = VerificationContext::new();
    for v in &["input_size", "heap_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("is", "input_size == 100"));
    ctx.push_obligation(ProofObligation::assume("hs_def", "heap_size == input_size"));
    ctx.push_obligation(ProofObligation::assert("same", "heap_size == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "build heap: all 100 elements present");
}

#[test]
fn decrease_key_maintains_order() {
    let mut ctx = VerificationContext::new();
    for v in &["old_key", "new_key", "parent_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ok", "old_key == 20"));
    ctx.push_obligation(ProofObligation::assume("nk", "new_key == 5"));
    ctx.push_obligation(ProofObligation::assume("pk", "parent_key == 3"));
    ctx.push_obligation(ProofObligation::assert("decreased", "new_key < old_key"));
    ctx.push_obligation(ProofObligation::assert(
        "parent_ok",
        "parent_key <= new_key",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decrease key: 20→5, parent 3 <= 5");
}
