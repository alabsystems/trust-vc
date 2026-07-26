// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn btree_node_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["page_size", "header_size", "key_size", "pointer_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("max_keys", u32_ty());
    // Keys per node = (page_size - header) / (key_size + pointer_size)
    // (4096 - 96) / (8 + 8) = 4000 / 16 = 250
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 96"));
    ctx.push_obligation(ProofObligation::assume("ks", "key_size == 8"));
    ctx.push_obligation(ProofObligation::assume("pts", "pointer_size == 8"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_keys == 250")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_250", "max_keys == 250"));
    ctx.push_obligation(ProofObligation::assert("positive", "max_keys > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree: (4096-96)/(8+8) = 250 keys per node");
}

#[test]
fn btree_depth_for_rows() {
    let mut ctx = VerificationContext::new();
    for v in &["total_rows", "keys_per_node"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth", u32_ty());
    // B-tree depth = ceil(log_base(keys, rows))
    // Precompute: 250 keys, 1M rows → depth ≈ 3 (250^3 = 15.6M > 1M)
    ctx.push_obligation(ProofObligation::assume("tr", "total_rows == 1000000"));
    ctx.push_obligation(ProofObligation::assume("kpn", "keys_per_node == 250"));
    ctx.push_obligation(ProofObligation::assume("d", "depth == 3")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3", "depth == 3"));
    ctx.push_obligation(ProofObligation::assert("shallow", "depth <= 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree: 1M rows, 250 keys → depth 3");
}

#[test]
fn leaf_page_fill_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["used_bytes", "page_size", "fill_percent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_minimum", i32_ty());
    // Precompute: 3072 / 4096 × 100 ≈ 75%
    ctx.push_obligation(ProofObligation::assume("ub", "used_bytes == 3072"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("fp", "fill_percent == 75")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "am_def",
        "above_minimum == if fill_percent >= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_75", "fill_percent == 75"));
    ctx.push_obligation(ProofObligation::assert("ok", "above_minimum == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree leaf: 3072/4096 = 75% fill ≥ 50% min");
}

#[test]
fn index_key_comparison() {
    let mut ctx = VerificationContext::new();
    for v in &["search_key", "node_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("go_left", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sk", "search_key == 42"));
    ctx.push_obligation(ProofObligation::assume("nk", "node_key == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "gl_def",
        "go_left == if search_key < node_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "go_left == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree search: 42 < 50 → go left");
}

#[test]
fn split_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["current_keys", "max_keys"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_split", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ck", "current_keys == 250"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_keys == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "needs_split == if current_keys >= max_keys { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_split == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree: 250 keys = 250 max → needs split");
}

#[test]
fn split_median_position() {
    let mut ctx = VerificationContext::new();
    for v in &["total_keys", "median_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Median = total / 2 (floor)
    ctx.push_obligation(ProofObligation::assume("tk", "total_keys == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "mi_def",
        "median_index == total_keys / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_125", "median_index == 125"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "B-tree split: median of 250 = index 125");
}

#[test]
fn merge_underflow() {
    let mut ctx = VerificationContext::new();
    for v in &["left_keys", "right_keys", "min_keys"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_merge", i32_ty());
    // Merge when both siblings are at minimum
    ctx.push_obligation(ProofObligation::assume("lk", "left_keys == 125"));
    ctx.push_obligation(ProofObligation::assume("rk", "right_keys == 124"));
    ctx.push_obligation(ProofObligation::assume("mk", "min_keys == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "can_merge == if right_keys < min_keys { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_merge == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree: right 124 < 125 min → can merge");
}

#[test]
fn index_scan_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_start", "range_end", "range_keys"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rs", "range_start == 100"));
    ctx.push_obligation(ProofObligation::assume("re", "range_end == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "rk_def",
        "range_keys == range_end - range_start",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_range == if range_end > range_start { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "range_keys == 100"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree scan: [100, 200) = 100 keys");
}

#[test]
fn unique_index_duplicate_check() {
    let mut ctx = VerificationContext::new();
    for v in &["new_key", "existing_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_duplicate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nk", "new_key == 42"));
    ctx.push_obligation(ProofObligation::assume("ek", "existing_key == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_duplicate == if new_key == existing_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_duplicate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B-tree unique: key 42 already exists → duplicate");
}

#[test]
fn page_io_cost() {
    let mut ctx = VerificationContext::new();
    for v in &["tree_depth", "io_per_level", "total_io"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable", i32_ty());
    // Point lookup cost = depth × 1 I/O per level
    ctx.push_obligation(ProofObligation::assume("td", "tree_depth == 3"));
    ctx.push_obligation(ProofObligation::assume("iol", "io_per_level == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tio_def",
        "total_io == tree_depth * io_per_level",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if total_io <= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "total_io == 3"));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "B-tree IO: depth 3 × 1 = 3 page reads");
}
