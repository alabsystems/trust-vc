// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn node_key_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["keys", "min_keys", "max_keys"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k", "keys == 3"));
    ctx.push_obligation(ProofObligation::assume("min", "min_keys == 2")); // ceil(order/2)-1
    ctx.push_obligation(ProofObligation::assume("max", "max_keys == 4")); // order - 1
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "keys >= min_keys && keys <= max_keys",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree node: 2 <= 3 keys <= 4");
}

#[test]
fn split_distributes_keys() {
    let mut ctx = VerificationContext::new();
    for v in &["total_keys", "left_keys", "right_keys", "promoted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tk", "total_keys == 5")); // overflow
    ctx.push_obligation(ProofObligation::assume("lk", "left_keys == 2"));
    ctx.push_obligation(ProofObligation::assume("p", "promoted == 1")); // middle key goes up
    ctx.push_obligation(ProofObligation::assume(
        "rk_def",
        "right_keys == total_keys - left_keys - promoted",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "right_keys == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "balanced",
        "left_keys == right_keys",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "split: 5 → 2 left + 1 promoted + 2 right");
}

#[test]
fn child_count_is_keys_plus_one() {
    let mut ctx = VerificationContext::new();
    for v in &["keys", "children"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k", "keys == 3"));
    ctx.push_obligation(ProofObligation::assume("c_def", "children == keys + 1"));
    ctx.push_obligation(ProofObligation::assert("is_4", "children == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree: 3 keys → 4 children");
}

#[test]
fn height_bounds_capacity() {
    // For order m, max keys at height h = m^(h+1) - 1
    // Simplified: at height 2, order 4: max = 4*4*4 - 1 = 63
    let mut ctx = VerificationContext::new();
    for v in &["height", "order", "min_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 2"));
    ctx.push_obligation(ProofObligation::assume("o", "order == 4"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_capacity == 63"));
    ctx.push_obligation(ProofObligation::assert("positive", "min_capacity > 0"));
    ctx.push_obligation(ProofObligation::assert("grows", "min_capacity > order"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "height 2, order 4: capacity 63 > 4");
}

#[test]
fn merge_combines_siblings() {
    let mut ctx = VerificationContext::new();
    for v in &["left_keys", "right_keys", "parent_key", "merged_keys"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lk", "left_keys == 1")); // underflow
    ctx.push_obligation(ProofObligation::assume("rk", "right_keys == 1"));
    ctx.push_obligation(ProofObligation::assume("pk", "parent_key == 1")); // pulled down
    ctx.push_obligation(ProofObligation::assume(
        "mk_def",
        "merged_keys == left_keys + right_keys + parent_key",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "merged_keys == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "merge: 1 + 1 + 1 parent = 3 merged keys");
}

#[test]
fn insertion_increases_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count_before", "count_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "count_before == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "count_after == count_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "count_after > count_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree insert: 100 → 101");
}

#[test]
fn deletion_decreases_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count_before", "count_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "count_before == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "count_after == count_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "decreases",
        "count_after < count_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree delete: 100 → 99");
}

#[test]
fn leaf_depth_uniform() {
    // All leaves at same depth in a valid B-tree
    let mut ctx = VerificationContext::new();
    for v in &["leaf1_depth", "leaf2_depth", "leaf3_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d1", "leaf1_depth == 3"));
    ctx.push_obligation(ProofObligation::assume("d2", "leaf2_depth == 3"));
    ctx.push_obligation(ProofObligation::assume("d3", "leaf3_depth == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "uniform",
        "leaf1_depth == leaf2_depth && leaf2_depth == leaf3_depth",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "all leaves at depth 3");
}

#[test]
fn search_path_bounded_by_height() {
    let mut ctx = VerificationContext::new();
    for v in &["comparisons", "height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 4"));
    ctx.push_obligation(ProofObligation::assume("c", "comparisons == 4")); // one per level
    ctx.push_obligation(ProofObligation::assert("bounded", "comparisons <= height"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "search: 4 comparisons <= height 4");
}

#[test]
fn rebalance_preserves_total() {
    let mut ctx = VerificationContext::new();
    for v in &["left_before", "right_before", "left_after", "right_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "left_before == 1"));
    ctx.push_obligation(ProofObligation::assume("rb", "right_before == 5"));
    // Rotate: move one from right to left
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "left_after == left_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "right_after == right_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "left_after + right_after == left_before + right_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rebalance: 1+5 = 2+4, total preserved");
}
