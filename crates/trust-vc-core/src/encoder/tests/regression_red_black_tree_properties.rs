// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn root_is_black() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("root_color", u32_ty()); // 0=black, 1=red
    ctx.push_obligation(ProofObligation::assume("rc", "root_color == 0")); // invariant
    ctx.push_obligation(ProofObligation::assert("black", "root_color == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB tree: root is black (0)");
}

#[test]
fn red_node_has_black_children() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_color", "left_child_color", "right_child_color"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "parent_color == 1")); // red
    ctx.push_obligation(ProofObligation::assume("lcc", "left_child_color == 0")); // black
    ctx.push_obligation(ProofObligation::assume("rcc", "right_child_color == 0")); // black
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if parent_color == 1 && left_child_color == 0 && right_child_color == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB: red parent → both children black");
}

#[test]
fn black_height_equal() {
    let mut ctx = VerificationContext::new();
    for v in &["left_black_height", "right_black_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lbh", "left_black_height == 3"));
    ctx.push_obligation(ProofObligation::assume("rbh", "right_black_height == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "equal",
        "left_black_height == right_black_height",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB: black height 3 == 3 (balanced)");
}

#[test]
fn insertion_may_increase_height() {
    let mut ctx = VerificationContext::new();
    for v in &["old_black_height", "new_black_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("height_changed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("obh", "old_black_height == 3"));
    ctx.push_obligation(ProofObligation::assume("nbh", "new_black_height == 4")); // root split
    ctx.push_obligation(ProofObligation::assume(
        "hc_def",
        "height_changed == if new_black_height > old_black_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "new_black_height == 4"));
    ctx.push_obligation(ProofObligation::assert("increased", "height_changed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB insert: black height 3 → 4 (root split)");
}

#[test]
fn max_height_bound() {
    // RB tree height <= 2 * log2(n + 1)
    let mut ctx = VerificationContext::new();
    for v in &["num_nodes", "max_height", "actual_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_bound", i32_ty());
    // For n=15: max_height = 2*log2(16) = 2*4 = 8
    ctx.push_obligation(ProofObligation::assume("nn", "num_nodes == 15"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_height == 8")); // 2*log2(16) = 8
    ctx.push_obligation(ProofObligation::assume("ah", "actual_height == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_bound == if actual_height <= max_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_bound == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB height: 5 <= 8 (2*log2(16)) → within bound");
}

#[test]
fn rotation_preserves_bst() {
    // Left rotation: parent.right becomes parent, parent becomes left child
    let mut ctx = VerificationContext::new();
    for v in &["parent_key", "right_child_key", "left_subtree_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bst_preserved", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pk", "parent_key == 10"));
    ctx.push_obligation(ProofObligation::assume("rck", "right_child_key == 15"));
    ctx.push_obligation(ProofObligation::assume("lsm", "left_subtree_max == 8"));
    // After left rotation: right_child (15) is new root, parent (10) is left child
    // BST property: left_subtree_max (8) < parent (10) < right_child (15)
    ctx.push_obligation(ProofObligation::assume(
        "bp_def",
        "bst_preserved == if left_subtree_max < parent_key && parent_key < right_child_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "bst_preserved == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation: 8 < 10 < 15 → BST preserved");
}

#[test]
fn recoloring_fixes_double_red() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_old", "uncle_old", "grandparent_old"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    for v in &["parent_new", "uncle_new", "grandparent_new"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Case 1: recolor parent and uncle to black, grandparent to red
    ctx.push_obligation(ProofObligation::assume("po", "parent_old == 1")); // red
    ctx.push_obligation(ProofObligation::assume("uo", "uncle_old == 1")); // red
    ctx.push_obligation(ProofObligation::assume("go", "grandparent_old == 0")); // black
    ctx.push_obligation(ProofObligation::assume("pn", "parent_new == 0")); // → black
    ctx.push_obligation(ProofObligation::assume("un", "uncle_new == 0")); // → black
    ctx.push_obligation(ProofObligation::assume("gn", "grandparent_new == 1")); // → red
    ctx.push_obligation(ProofObligation::assert("parent_fixed", "parent_new == 0"));
    ctx.push_obligation(ProofObligation::assert("uncle_fixed", "uncle_new == 0"));
    ctx.push_obligation(ProofObligation::assert("gp_red", "grandparent_new == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "recolor: parent+uncle → black, grandparent → red");
}

#[test]
fn node_count_after_insert() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "new_count == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "increased",
        "new_count > old_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB insert: 15 → 16 nodes");
}

#[test]
fn node_count_after_delete() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "new_count == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "new_count < old_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB delete: 16 → 15 nodes");
}

#[test]
fn minimum_nodes_for_black_height() {
    // Minimum nodes for black height h: 2^h - 1 (all-black perfect tree)
    let mut ctx = VerificationContext::new();
    for v in &["black_height", "min_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // For bh=3: min = 2^3 - 1 = 7 (hardcoded)
    ctx.push_obligation(ProofObligation::assume("bh", "black_height == 3"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_nodes == 7")); // 2^3 - 1
    ctx.push_obligation(ProofObligation::assert("is_7", "min_nodes == 7"));
    ctx.push_obligation(ProofObligation::assert("positive", "min_nodes > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RB: min nodes for bh=3 is 2^3-1=7");
}
