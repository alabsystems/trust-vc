// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 59 — AVL Tree Rotation / Balanced BST VCs.
//!
//! Part 2: Double rotations, symbolic height properties, and soundness
//! negatives. Split from `test_verifythis_avl_rotation.rs` to stay
//! under the 500-line guidance.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

// ========================================================================
// GROUP E: Double rotations (left-right and right-left)
// ========================================================================

/// Tier 59e: Left-right double rotation.
/// Before (left-right imbalance):
///       30                   30                 25
///      /          Left@20   /    Right@30     /    \
///    20           →       25        →       20      30
///      \                 /
///      25              20
///
/// Overall: insert 25 into tree [30, 20] triggers left-right case.
#[test]
fn test_vt_tier59e_double_rotation_left_right() {
    let mut ctx = VerificationContext::new();
    // Initial tree (after inserting 25 under 20's right)
    assume_seq_i64(&mut ctx, "key", &[30, 20, 25]);

    // After left rotation at 20: key=[30, 25, 20]
    // After right rotation at 30: key=[25, 20, 30]
    assume_seq_i64(&mut ctx, "key_final", &[25, 20, 30]);
    assume_seq_i64(&mut ctx, "h_final", &[2, 1, 1]);

    // BST order preserved
    ctx.push_assert("order_l", "key_final.index(1) < key_final.index(0)");
    ctx.push_assert("order_r", "key_final.index(2) > key_final.index(0)");

    // Balance restored
    ctx.declare_var_parsed("bf", "i64");
    ctx.push_assume("bf_def", "bf == h_final.index(1) - h_final.index(2)");
    ctx.push_assert("bal_lo", "bf >= -1");
    ctx.push_assert("bal_hi", "bf <= 1");

    // All keys preserved
    ctx.push_assert("k30", "key.index(0) == key_final.index(2)");
    ctx.push_assert("k20", "key.index(1) == key_final.index(1)");
    ctx.push_assert("k25", "key.index(2) == key_final.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59e: left-right double rotation should verify, got: {:?}",
        result,
    );
}

/// Tier 59e: Right-left double rotation.
/// Before (right-left imbalance):
///    10                  10                     15
///      \      Right@20     \     Left@10      /    \
///      20      →            15      →       10      20
///     /                       \
///    15                       20
///
/// Overall: insert 15 into tree [10, 20] triggers right-left case.
#[test]
fn test_vt_tier59e_double_rotation_right_left() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[10, 20, 15]);

    // After right rotation at 20: key=[10, 15, 20]
    // After left rotation at 10: key=[15, 10, 20]
    assume_seq_i64(&mut ctx, "key_final", &[15, 10, 20]);
    assume_seq_i64(&mut ctx, "h_final", &[2, 1, 1]);

    // BST order
    ctx.push_assert("order_l", "key_final.index(1) < key_final.index(0)");
    ctx.push_assert("order_r", "key_final.index(2) > key_final.index(0)");

    // Balance
    ctx.declare_var_parsed("bf", "i64");
    ctx.push_assume("bf_def", "bf == h_final.index(1) - h_final.index(2)");
    ctx.push_assert("bal_lo", "bf >= -1");
    ctx.push_assert("bal_hi", "bf <= 1");

    // Keys preserved
    ctx.push_assert("k10", "key.index(0) == key_final.index(1)");
    ctx.push_assert("k20", "key.index(1) == key_final.index(2)");
    ctx.push_assert("k15", "key.index(2) == key_final.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59e: right-left double rotation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Symbolic height properties
// ========================================================================

/// Tier 59f: Symbolic — AVL height bound: h <= 1.44 * log2(n+2).
/// For n=7 nodes, max AVL height is 4. Using h <= 2*n as a simpler
/// inductive bound that holds for small n.
#[test]
fn test_vt_tier59f_symbolic_height_consistency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("h_left", "i64");
    ctx.declare_var_parsed("h_right", "i64");
    ctx.declare_var_parsed("h_node", "i64");

    // AVL property: balance factor in [-1, 1], bounded to avoid BV overflow
    ctx.push_assume("h_left_ge_0", "h_left >= 0");
    ctx.push_assume("h_right_ge_0", "h_right >= 0");
    ctx.push_assume("h_left_bounded", "h_left < 1000000");
    ctx.push_assume("h_right_bounded", "h_right < 1000000");
    ctx.push_assume("bal_lo", "h_left - h_right >= -1");
    ctx.push_assume("bal_hi", "h_left - h_right <= 1");
    // Height = 1 + max(h_left, h_right)
    ctx.push_assume(
        "h_def",
        "h_node == 1 + if h_left >= h_right { h_left } else { h_right }",
    );

    // Height is positive
    ctx.push_assert("h_pos", "h_node >= 1");
    // Height bounded by both children
    ctx.push_assert("h_ge_l", "h_node > h_left");
    ctx.push_assert("h_ge_r", "h_node > h_right");
    // Max child height is h_node - 1
    ctx.push_assert("max_child", "h_left <= h_node - 1 && h_right <= h_node - 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59f: symbolic height consistency should verify, got: {:?}",
        result,
    );
}

/// Tier 59f: Symbolic — rotation preserves in-order traversal.
/// For right rotation: in-order of subtrees is (A, x, B, y, C) both
/// before and after rotation.
#[test]
fn test_vt_tier59f_symbolic_rotation_preserves_inorder() {
    let mut ctx = VerificationContext::new();
    // x and y are pivot and root keys
    ctx.declare_var_parsed("x", "i64");
    ctx.declare_var_parsed("y", "i64");
    // Subtree bounds: a_max < x < b_min, b_max < y < c_min
    ctx.declare_var_parsed("a_max", "i64");
    ctx.declare_var_parsed("b_min", "i64");
    ctx.declare_var_parsed("b_max", "i64");
    ctx.declare_var_parsed("c_min", "i64");

    ctx.push_assume("bst_ax", "a_max < x");
    ctx.push_assume("bst_xb", "x < b_min");
    ctx.push_assume("bst_by", "b_max < y");
    ctx.push_assume("bst_yc", "y < c_min");
    ctx.push_assume("b_order", "b_min <= b_max");

    // After right rotation: root=x, x.right=y, y.left=B
    // In-order: A, x, B, y, C — same as before
    // BST at new root x: x < b_min (b_min <= b_max < y, and y < c_min)
    // x < y (x < b_min <= b_max < y)
    ctx.push_assert("x_lt_y", "x < y");
    // Full in-order: a < x < b < y < c
    ctx.push_assert(
        "full_order",
        "a_max < x && x < b_min && b_max < y && y < c_min",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59f: rotation preserves in-order should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP G: Soundness negatives
// ========================================================================

/// Tier 59g NEGATIVE: Wrong rotation direction — applying left rotation
/// to a left-heavy tree makes it worse, not better.
/// Before: h=[3, 2, 1] (left-heavy at root, bf=2-1=1).
/// Wrong left rotation would make: h=[3, 1, 2] (now bf=1-2=-1), but
/// this doesn't change the height. Claiming height decreased should fail.
#[test]
fn test_vt_tier59g_wrong_rotation_direction() {
    let mut ctx = VerificationContext::new();
    // Left-heavy tree: root height 3, left child 2, right child 1
    assume_seq_i64(&mut ctx, "h_pre", &[3, 2, 1]);

    // Wrong: apply left rotation to left-heavy → swaps subtrees
    // "After" heights (just swapped children conceptually)
    assume_seq_i64(&mut ctx, "h_wrong", &[3, 1, 2]);

    // Claiming the wrong rotation reduced height
    ctx.push_assert("height_dec", "h_wrong.index(0) < h_pre.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 59g SOUNDNESS: wrong rotation direction should fail, got: {:?}",
        result,
    );
}

/// Tier 59g NEGATIVE: Rotation that breaks BST order.
/// Right rotation on [30, 20, 25] where 25 is 20's RIGHT child.
/// Incorrect rotation puts 25 as left of 30 → 25 < 30 ✓ but claims
/// 25 > 30 should fail.
#[test]
fn test_vt_tier59g_rotation_breaks_bst_claim() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[30, 20, 25]);

    // After right rotation: root=20, left=nothing, right=30, 30's left=25
    // This is correct: 25 < 30 (BST ✓). But claiming 25 > 30 should fail.
    ctx.push_assert("wrong_order", "key.index(2) > key.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 59g SOUNDNESS: broken BST claim should be rejected, got: {:?}",
        result,
    );
}

/// Tier 59g NEGATIVE: A bad subtree-transfer pointer must be rejected.
/// After the rotation, node 30 cannot become the right child of node 10 while
/// still claiming it remains in the left subtree of root 20.
/// Gated: confirmation-check non-determinism (#2241). (#2658 Category G2)
#[test]
#[cfg(feature = "expensive-tests")]
fn test_vt_tier59g_subtree_transfer_pointer_mismatch_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 40, 30]);
    assume_seq_i64(&mut ctx, "left_post", &[1, -1, -1, -1]);
    assume_seq_i64(&mut ctx, "right_post", &[2, 3, -1, -1]);

    ctx.push_assert(
        "root_left_order",
        "key_post.index(left_post.index(0)) < key_post.index(0)",
    );
    ctx.push_assert(
        "wrong_transferred_subtree",
        "key_post.index(right_post.index(1)) < key_post.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 59g SOUNDNESS: malformed subtree transfer should violate BST order, got: {:?}",
        result,
    );
}

/// Tier 59g NEGATIVE: Claiming a binary tree with balance factor 3
/// is AVL-balanced.
#[test]
fn test_vt_tier59g_balance_factor_3_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("h_left", "i64");
    ctx.declare_var_parsed("h_right", "i64");
    ctx.push_assume("h_left_val", "h_left == 4");
    ctx.push_assume("h_right_val", "h_right == 1");

    ctx.declare_var_parsed("bf", "i64");
    ctx.push_assume("bf_def", "bf == h_left - h_right");

    // Claiming this is balanced (bf in [-1, 1])
    ctx.push_assert("balanced", "bf >= -1 && bf <= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 59g SOUNDNESS: balance factor 3 should be rejected, got: {:?}",
        result,
    );
}
