// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn leaf_node_has_no_children() {
    let mut ctx = VerificationContext::new();
    for v in &["left", "right"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_leaf", i32_ty());
    // 0 = null/no child
    ctx.push_obligation(ProofObligation::assume("l", "left == 0"));
    ctx.push_obligation(ProofObligation::assume("r", "right == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "leaf_def",
        "is_leaf == if left == 0 && right == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_leaf_node", "is_leaf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "node with no children is a leaf");
}

#[test]
fn full_binary_tree_nodes() {
    // Full binary tree of height h has 2^(h+1) - 1 nodes
    // Height 2: 7 nodes
    let mut ctx = VerificationContext::new();
    for v in &["height", "nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 2"));
    ctx.push_obligation(ProofObligation::assume("n_val", "nodes == 7"));
    ctx.push_obligation(ProofObligation::assert("is_7", "nodes == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "full binary tree height 2 has 7 nodes");
}

#[test]
fn binary_tree_max_leaves() {
    // Max leaves at height h = 2^h
    // Height 3: max 8 leaves
    let mut ctx = VerificationContext::new();
    for v in &["height", "max_leaves"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 3"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_leaves == 8"));
    ctx.push_obligation(ProofObligation::assert("is_8", "max_leaves == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "binary tree height 3: max 8 leaves");
}

#[test]
fn internal_nodes_plus_one_equals_leaves() {
    // In full binary tree: leaves = internal_nodes + 1
    let mut ctx = VerificationContext::new();
    for v in &["internal", "leaves"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("int", "internal == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "leaves_def",
        "leaves == internal + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "leaves == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "full binary tree: 6 internal → 7 leaves");
}

#[test]
fn tree_total_nodes() {
    let mut ctx = VerificationContext::new();
    for v in &["internal", "leaves", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("int", "internal == 3"));
    ctx.push_obligation(ProofObligation::assume("lv", "leaves == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == internal + leaves",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "total == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 internal + 4 leaves = 7 total");
}

#[test]
fn bst_property() {
    // BST: left < parent < right
    let mut ctx = VerificationContext::new();
    for v in &["left_val", "parent_val", "right_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left_val == 3"));
    ctx.push_obligation(ProofObligation::assume("p", "parent_val == 5"));
    ctx.push_obligation(ProofObligation::assume("r", "right_val == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "bst",
        "left_val < parent_val && parent_val < right_val",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BST: 3 < 5 < 8");
}

#[test]
fn tree_depth_from_path() {
    // Depth = number of edges from root to node
    let mut ctx = VerificationContext::new();
    for v in &["root_depth", "child_depth", "grandchild_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rd", "root_depth == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "child_depth == root_depth + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "gd_def",
        "grandchild_depth == child_depth + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("gd_is_2", "grandchild_depth == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "grandchild depth = 2");
}

#[test]
fn balanced_tree_height_bound() {
    // Balanced binary tree with n nodes: height <= log2(n)
    // 15 nodes → height <= 3 (since 2^4 - 1 = 15)
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "height", "max_nodes_at_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n", "nodes == 15"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 3"));
    // 2^(3+1) - 1 = 15 nodes fit in height 3
    ctx.push_obligation(ProofObligation::assume(
        "max_def",
        "max_nodes_at_height == 15",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fits",
        "nodes <= max_nodes_at_height",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 nodes fit in balanced tree of height 3");
}

#[test]
fn subtree_size_sum() {
    // Parent subtree size = left_size + right_size + 1
    let mut ctx = VerificationContext::new();
    for v in &["left_size", "right_size", "parent_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ls", "left_size == 3"));
    ctx.push_obligation(ProofObligation::assume("rs", "right_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ps_def",
        "parent_size == left_size + right_size + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "parent_size == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "subtree: 3 + 4 + 1 = 8");
}

#[test]
fn heap_parent_index() {
    // In array-backed heap: parent(i) = (i-1)/2
    let mut ctx = VerificationContext::new();
    for v in &["child", "parent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "child == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "parent == (child - 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "parent == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "heap parent of 6 = (6-1)/2 = 2");
}
