// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn balance_factor_range() {
    let mut ctx = VerificationContext::new();
    for v in &["left_height", "right_height", "balance_factor"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lh", "left_height == 3"));
    ctx.push_obligation(ProofObligation::assume("rh", "right_height == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "bf_def",
        "balance_factor == right_height - left_height",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if balance_factor >= 0 - 1 && balance_factor <= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bf_1", "balance_factor == 1"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL: bf = 4-3 = 1, within [-1,1]");
}

#[test]
fn left_rotation_rebalance() {
    let mut ctx = VerificationContext::new();
    for v in &["old_bf", "new_bf"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Right-heavy node (bf=2) → left rotation → balanced (bf=0)
    ctx.push_obligation(ProofObligation::assume("obf", "old_bf == 2"));
    ctx.push_obligation(ProofObligation::assume("nbf", "new_bf == 0")); // after rotation
    ctx.push_obligation(ProofObligation::assert("balanced", "new_bf == 0"));
    ctx.push_obligation(ProofObligation::assert("improved", "new_bf < old_bf"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL left rotation: bf 2 → 0");
}

#[test]
fn right_rotation_rebalance() {
    let mut ctx = VerificationContext::new();
    for v in &["old_bf", "new_bf"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Left-heavy node (bf=-2) → right rotation → balanced (bf=0)
    ctx.push_obligation(ProofObligation::assume("obf", "old_bf == 0 - 2"));
    ctx.push_obligation(ProofObligation::assume("nbf", "new_bf == 0"));
    ctx.push_obligation(ProofObligation::assert("balanced", "new_bf == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL right rotation: bf -2 → 0");
}

#[test]
fn height_after_insert() {
    let mut ctx = VerificationContext::new();
    for v in &["old_height", "new_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("grew", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oh", "old_height == 5"));
    ctx.push_obligation(ProofObligation::assume("nh", "new_height == 6")); // grew by 1
    ctx.push_obligation(ProofObligation::assume(
        "g_def",
        "grew == if new_height > old_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "new_height == 6"));
    ctx.push_obligation(ProofObligation::assert("yes", "grew == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL insert: height 5 → 6");
}

#[test]
fn max_height_for_nodes() {
    // AVL height <= 1.44 * log2(n+2) - 0.328
    // For n=100: max height ≈ 1.44 * 6.67 - 0.328 ≈ 9.3 → 9
    let mut ctx = VerificationContext::new();
    for v in &["num_nodes", "actual_height", "max_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_bound", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nn", "num_nodes == 100"));
    ctx.push_obligation(ProofObligation::assume("ah", "actual_height == 7"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_height == 9")); // theoretical max
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_bound == if actual_height <= max_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_bound == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL: height 7 <= 9 max for 100 nodes");
}

#[test]
fn double_rotation_left_right() {
    // Left-right case: left rotate child, then right rotate parent
    let mut ctx = VerificationContext::new();
    for v in &["parent_bf", "child_bf", "final_bf"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pbf", "parent_bf == 0 - 2")); // left-heavy
    ctx.push_obligation(ProofObligation::assume("cbf", "child_bf == 1")); // right-heavy child
    ctx.push_obligation(ProofObligation::assume("fbf", "final_bf == 0")); // balanced after double rotation
    ctx.push_obligation(ProofObligation::assert("balanced", "final_bf == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL: left-right double rotation → bf=0");
}

#[test]
fn bst_ordering_preserved() {
    let mut ctx = VerificationContext::new();
    for v in &["left_key", "node_key", "right_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ordered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lk", "left_key == 10"));
    ctx.push_obligation(ProofObligation::assume("nk", "node_key == 20"));
    ctx.push_obligation(ProofObligation::assume("rk", "right_key == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "ordered == if left_key < node_key && node_key < right_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "ordered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL BST: 10 < 20 < 30");
}

#[test]
fn min_nodes_for_height() {
    // Minimum nodes for AVL height h: N(h) = N(h-1) + N(h-2) + 1
    // N(0)=1, N(1)=2, N(2)=4, N(3)=7, N(4)=12, N(5)=20
    let mut ctx = VerificationContext::new();
    for v in &["height", "min_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "height == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_nodes == 20")); // N(5) = 20
    ctx.push_obligation(ProofObligation::assert("is_20", "min_nodes == 20"));
    ctx.push_obligation(ProofObligation::assert("positive", "min_nodes > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL min nodes: N(5) = 20");
}

#[test]
fn deletion_may_decrease_height() {
    let mut ctx = VerificationContext::new();
    for v in &["old_height", "new_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shrunk", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oh", "old_height == 6"));
    ctx.push_obligation(ProofObligation::assume("nh", "new_height == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shrunk == if new_height < old_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "new_height == 5"));
    ctx.push_obligation(ProofObligation::assert("yes", "shrunk == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL delete: height 6 → 5");
}

#[test]
fn node_count_invariant() {
    // nodes = left_count + right_count + 1
    let mut ctx = VerificationContext::new();
    for v in &["left_count", "right_count", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lc", "left_count == 12"));
    ctx.push_obligation(ProofObligation::assume("rc", "right_count == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == left_count + right_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "total == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AVL: 12 + 7 + 1 = 20 nodes");
}
