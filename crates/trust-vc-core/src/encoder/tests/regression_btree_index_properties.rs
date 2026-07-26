// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn leaf_chain_linked() {
    // B+tree leaves form a linked list
    let mut ctx = VerificationContext::new();
    for v in &["leaf1_next", "leaf2_id", "leaf2_next", "leaf3_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l1n", "leaf1_next == 2")); // points to leaf2
    ctx.push_obligation(ProofObligation::assume("l2i", "leaf2_id == 2"));
    ctx.push_obligation(ProofObligation::assume("l2n", "leaf2_next == 3")); // points to leaf3
    ctx.push_obligation(ProofObligation::assume("l3i", "leaf3_id == 3"));
    ctx.push_obligation(ProofObligation::assert("chain1", "leaf1_next == leaf2_id"));
    ctx.push_obligation(ProofObligation::assert("chain2", "leaf2_next == leaf3_id"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B+tree leaf chain: 1→2→3");
}

#[test]
fn internal_node_fanout() {
    let mut ctx = VerificationContext::new();
    for v in &["keys", "children"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k", "keys == 100"));
    ctx.push_obligation(ProofObligation::assume("c_def", "children == keys + 1"));
    ctx.push_obligation(ProofObligation::assert("is_101", "children == 101"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B+tree internal: 100 keys → 101 children");
}

#[test]
fn leaf_fill_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["keys_in_leaf", "max_keys", "fill_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("kil", "keys_in_leaf == 75"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_keys == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "fill_pct == keys_in_leaf * 100 / max_keys",
    ));
    ctx.push_obligation(ProofObligation::assert("is_75", "fill_pct == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "fill factor: 75/100 * 100 = 75%");
}

#[test]
fn range_scan_covers_leaves() {
    let mut ctx = VerificationContext::new();
    for v in &["start_leaf", "end_leaf", "leaves_scanned"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sl", "start_leaf == 5"));
    ctx.push_obligation(ProofObligation::assume("el", "end_leaf == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ls_def",
        "leaves_scanned == end_leaf - start_leaf + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "leaves_scanned == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "range scan: leaves 5-12 = 8 leaves");
}

#[test]
fn index_lookup_io_count() {
    let mut ctx = VerificationContext::new();
    for v in &["height", "io_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 3"));
    ctx.push_obligation(ProofObligation::assume("io_def", "io_count == height + 1")); // internal + leaf
    ctx.push_obligation(ProofObligation::assert("is_4", "io_count == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "B+tree lookup: height 3 = 4 I/Os");
}

#[test]
fn split_leaf_redistributes() {
    let mut ctx = VerificationContext::new();
    for v in &["original_keys", "left_keys", "right_keys", "separator_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ok", "original_keys == 101")); // overflow
    ctx.push_obligation(ProofObligation::assume("lk", "left_keys == 50"));
    ctx.push_obligation(ProofObligation::assume("sk", "separator_key == 1")); // copy up
    ctx.push_obligation(ProofObligation::assume(
        "rk_def",
        "right_keys == original_keys - left_keys",
    ));
    ctx.push_obligation(ProofObligation::assert("is_51", "right_keys == 51"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leaf split: 101 → 50 left + 51 right");
}

#[test]
fn bulk_load_fill_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["total_records", "records_per_leaf", "leaves_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tr", "total_records == 10000"));
    ctx.push_obligation(ProofObligation::assume("rpl", "records_per_leaf == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ln_def",
        "leaves_needed == total_records / records_per_leaf",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "leaves_needed == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bulk load: 10000 / 100 = 100 leaves");
}

#[test]
fn clustered_index_row_locality() {
    // Clustered index: adjacent keys → adjacent pages
    let mut ctx = VerificationContext::new();
    for v in &["key1_page", "key2_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("same_page", i32_ty());
    ctx.push_obligation(ProofObligation::assume("k1p", "key1_page == 42"));
    ctx.push_obligation(ProofObligation::assume("k2p", "key2_page == 42")); // adjacent keys same page
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "same_page == if key1_page == key2_page { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("local", "same_page == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clustered: adjacent keys on same page 42");
}

#[test]
fn secondary_index_pointer_count() {
    let mut ctx = VerificationContext::new();
    for v in &["index_entries", "matching_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ie", "index_entries == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "mr_def",
        "matching_rows == index_entries",
    )); // 1:1 for unique index
    ctx.push_obligation(ProofObligation::assert("is_50", "matching_rows == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "secondary index: 50 entries → 50 rows");
}

#[test]
fn page_utilization_after_deletes() {
    let mut ctx = VerificationContext::new();
    for v in &["initial_keys", "deleted", "remaining", "page_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_merge", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ik", "initial_keys == 100"));
    ctx.push_obligation(ProofObligation::assume("d", "deleted == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == initial_keys - deleted",
    ));
    ctx.push_obligation(ProofObligation::assume("pc", "page_capacity == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nm_def",
        "needs_merge == if remaining < page_capacity / 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("merge", "needs_merge == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "40 remaining < 50 (100/2) → needs merge");
}
