// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 60 — Red-Black Tree Insert Fixup VCs.
//!
//! Red-black trees refine BSTs with color and black-height invariants:
//!   - the root is black
//!   - no red node has a red child
//!   - every root-to-null path has the same black height
//!   - recoloring and rotations preserve BST order plus color validity
//!
//! We model trees with flat arrays:
//!   - `key: Seq<i64>` — node keys
//!   - `color: Seq<i64>` — `0 = BLACK`, `1 = RED`
//!   - `bh: Seq<i64>` — black height, where red leaves contribute `0`
//!     and black leaves contribute `1`
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

const BLACK: i64 = 0;
const RED: i64 = 1;

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
// GROUP A: Root-black and BST-order invariants
// ========================================================================

/// Tier 60a: a 3-node red-black tree keeps a black root and BST order.
#[test]
fn test_vt_tier60a_root_black_bst_order_3node() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[20, 10, 30]);
    assume_seq_i64(&mut ctx, "color", &[BLACK, RED, RED]);

    ctx.push_assert("root_black", "color.index(0) == 0");
    ctx.push_assert("left_lt_root", "key.index(1) < key.index(0)");
    ctx.push_assert("root_lt_right", "key.index(0) < key.index(2)");
    ctx.push_assert(
        "children_may_be_red",
        "color.index(1) == 1 && color.index(2) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60a: root-black 3-node tree should verify, got: {:?}",
        result,
    );
}

/// Tier 60a: subtree ordering remains valid in a 5-node red-black tree.
#[test]
fn test_vt_tier60a_bst_order_5node_tree() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[20, 10, 30, 5, 15]);
    assume_seq_i64(&mut ctx, "color", &[BLACK, RED, BLACK, BLACK, BLACK]);

    ctx.push_assert("root_black", "color.index(0) == 0");
    ctx.push_assert("left_lt_root", "key.index(1) < key.index(0)");
    ctx.push_assert("root_lt_right", "key.index(0) < key.index(2)");
    ctx.push_assert("left_left_lt_parent", "key.index(3) < key.index(1)");
    ctx.push_assert("parent_lt_left_right", "key.index(1) < key.index(4)");
    ctx.push_assert("left_subtree_lt_root_3", "key.index(3) < key.index(0)");
    ctx.push_assert("left_subtree_lt_root_4", "key.index(4) < key.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60a: BST order 5-node tree should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Red-parent constraints
// ========================================================================

/// Tier 60b: a red internal node may exist only with black children.
#[test]
fn test_vt_tier60b_red_internal_node_has_black_children() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[20, 10, 30, 5, 15]);
    assume_seq_i64(&mut ctx, "color", &[BLACK, RED, BLACK, BLACK, BLACK]);

    ctx.push_assert("parent_is_red", "color.index(1) == 1");
    ctx.push_assert("root_is_black", "color.index(0) == 0");
    ctx.push_assert("left_child_black", "color.index(3) == 0");
    ctx.push_assert("right_child_black", "color.index(4) == 0");
    ctx.push_assert(
        "no_red_red",
        "!(color.index(1) == 1 && color.index(3) == 1) && \
         !(color.index(1) == 1 && color.index(4) == 1)",
    );
    ctx.push_assert(
        "order_5_10_15",
        "key.index(3) < key.index(1) && key.index(1) < key.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60b: red internal node with black children should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Black-height invariants
// ========================================================================

/// Tier 60c: black-height agrees across both subtrees of a valid 5-node tree.
#[test]
fn test_vt_tier60c_black_height_balanced_5node_tree() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "color", &[BLACK, RED, BLACK, BLACK, BLACK]);
    assume_seq_i64(&mut ctx, "bh", &[2, 1, 1, 1, 1]);

    // Red node 10 does not increase black height; both children are black leaves.
    ctx.push_assert("red_node_bh_matches_children", "bh.index(1) == bh.index(3)");
    ctx.push_assert(
        "red_node_bh_matches_other_child",
        "bh.index(1) == bh.index(4)",
    );
    // Root sees equal black height through left and right subtrees.
    ctx.push_assert("root_children_bh_equal", "bh.index(1) == bh.index(2)");
    ctx.push_assert("root_adds_one_black", "bh.index(0) == bh.index(1) + 1");
    ctx.push_assert(
        "right_leaf_black",
        "color.index(2) == 0 && bh.index(2) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60c: balanced black-height should verify, got: {:?}",
        result,
    );
}

/// Tier 60c: a single black root has black height one.
#[test]
fn test_vt_tier60c_single_black_root_has_bh_one() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[10]);
    assume_seq_i64(&mut ctx, "color", &[BLACK]);
    assume_seq_i64(&mut ctx, "bh", &[1]);

    ctx.push_assert("root_black", "color.index(0) == 0");
    ctx.push_assert("root_bh_one", "bh.index(0) == 1");
    ctx.push_assert("singleton_key_stable", "key.index(0) == 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60c: single black root should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Recolor fixups
// ========================================================================

/// Tier 60d: red-uncle recoloring at the root restores local validity.
#[test]
fn test_vt_tier60d_red_uncle_recolor_root_case() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_pre", &[20, 10, 30, 5]);
    assume_seq_i64(&mut ctx, "color_pre", &[BLACK, RED, RED, RED]);

    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30, 5]);
    assume_seq_i64(&mut ctx, "color_post", &[BLACK, BLACK, BLACK, RED]);
    assume_seq_i64(&mut ctx, "bh_post", &[2, 1, 1, 0]);

    ctx.push_assert("pre_parent_red", "color_pre.index(1) == 1");
    ctx.push_assert("pre_uncle_red", "color_pre.index(2) == 1");
    ctx.push_assert("post_root_black", "color_post.index(0) == 0");
    ctx.push_assert("post_parent_black", "color_post.index(1) == 0");
    ctx.push_assert("post_uncle_black", "color_post.index(2) == 0");
    ctx.push_assert("inserted_leaf_stays_red", "color_post.index(3) == 1");
    ctx.push_assert("keys_preserved_0", "key_pre.index(0) == key_post.index(0)");
    ctx.push_assert("keys_preserved_1", "key_pre.index(1) == key_post.index(1)");
    ctx.push_assert(
        "root_children_bh_equal",
        "bh_post.index(1) == bh_post.index(2)",
    );
    ctx.push_assert(
        "root_bh_increments",
        "bh_post.index(0) == bh_post.index(1) + 1",
    );
    ctx.push_assert(
        "no_red_red_post",
        "!(color_post.index(1) == 1 && color_post.index(3) == 1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60d: red-uncle recolor should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Rotation fixups
// ========================================================================

/// Tier 60e: right-right insertion uses a left rotation plus recoloring.
#[test]
fn test_vt_tier60e_left_rotation_fixup_right_right_case() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_pre", &[10, 20, 30]);
    assume_seq_i64(&mut ctx, "color_pre", &[BLACK, RED, RED]);

    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30]);
    assume_seq_i64(&mut ctx, "color_post", &[BLACK, RED, RED]);

    ctx.push_assert(
        "pre_violation",
        "color_pre.index(1) == 1 && color_pre.index(2) == 1",
    );
    ctx.push_assert("post_root_black", "color_post.index(0) == 0");
    ctx.push_assert(
        "post_children_red",
        "color_post.index(1) == 1 && color_post.index(2) == 1",
    );
    ctx.push_assert("bst_left", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("bst_right", "key_post.index(0) < key_post.index(2)");
    ctx.push_assert(
        "old_parent_becomes_root",
        "key_pre.index(1) == key_post.index(0)",
    );
    ctx.push_assert(
        "old_root_moves_left",
        "key_pre.index(0) == key_post.index(1)",
    );
    ctx.push_assert(
        "inserted_key_moves_right",
        "key_pre.index(2) == key_post.index(2)",
    );
    ctx.push_assert(
        "no_red_red_post",
        "!(color_post.index(0) == 1 && color_post.index(1) == 1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60e: left rotation fixup should verify, got: {:?}",
        result,
    );
}

/// Tier 60e: left-left insertion uses a right rotation plus recoloring.
#[test]
fn test_vt_tier60e_right_rotation_fixup_left_left_case() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_pre", &[30, 20, 10]);
    assume_seq_i64(&mut ctx, "color_pre", &[BLACK, RED, RED]);

    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30]);
    assume_seq_i64(&mut ctx, "color_post", &[BLACK, RED, RED]);

    ctx.push_assert(
        "pre_violation",
        "color_pre.index(1) == 1 && color_pre.index(2) == 1",
    );
    ctx.push_assert("post_root_black", "color_post.index(0) == 0");
    ctx.push_assert("bst_left", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("bst_right", "key_post.index(0) < key_post.index(2)");
    ctx.push_assert(
        "old_parent_becomes_root",
        "key_pre.index(1) == key_post.index(0)",
    );
    ctx.push_assert(
        "old_root_moves_right",
        "key_pre.index(0) == key_post.index(2)",
    );
    ctx.push_assert(
        "inserted_key_moves_left",
        "key_pre.index(2) == key_post.index(1)",
    );
    ctx.push_assert(
        "no_red_red_post",
        "!(color_post.index(0) == 1 && color_post.index(1) == 1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60e: right rotation fixup should verify, got: {:?}",
        result,
    );
}

/// Tier 60e: a transferred middle subtree stays ordered after rotation.
#[test]
fn test_vt_tier60e_rotation_with_middle_subtree_preserves_order() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30, 25]);
    assume_seq_i64(&mut ctx, "color_post", &[BLACK, RED, BLACK, RED]);

    ctx.push_assert("root_black", "color_post.index(0) == 0");
    ctx.push_assert("root_left_order", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("root_right_order", "key_post.index(0) < key_post.index(2)");
    ctx.push_assert(
        "middle_subtree_order",
        "key_post.index(0) < key_post.index(3)",
    );
    ctx.push_assert(
        "middle_is_left_of_30",
        "key_post.index(3) < key_post.index(2)",
    );
    ctx.push_assert(
        "black_parent_red_child_ok",
        "color_post.index(2) == 0 && color_post.index(3) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 60e: rotation with middle subtree should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 60f NEGATIVE: a red root violates the red-black root rule.
#[test]
fn test_vt_tier60f_root_red_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "color", &[RED, BLACK, BLACK]);

    ctx.push_assert("root_black", "color.index(0) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 60f SOUNDNESS: red root must be rejected, got: {:?}",
        result,
    );
}

/// Tier 60f NEGATIVE: a red node cannot have a red child.
#[test]
fn test_vt_tier60f_red_parent_with_red_child_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "color", &[BLACK, RED, BLACK, RED]);

    ctx.push_assert(
        "no_red_red",
        "!(color.index(1) == 1 && color.index(3) == 1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 60f SOUNDNESS: red parent with red child must fail, got: {:?}",
        result,
    );
}

/// Tier 60f NEGATIVE: unequal black heights invalidate the tree.
#[test]
fn test_vt_tier60f_black_height_mismatch_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "bh", &[2, 1, 0]);
    assume_seq_i64(&mut ctx, "color", &[BLACK, BLACK, RED]);

    ctx.push_assert("left_path_bh", "color.index(1) == 0 && bh.index(1) == 1");
    ctx.push_assert("right_path_bh", "color.index(2) == 1 && bh.index(2) == 0");
    ctx.push_assert("children_equal", "bh.index(1) == bh.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 60f SOUNDNESS: black-height mismatch must fail, got: {:?}",
        result,
    );
}

/// Tier 60f NEGATIVE: placing the transferred subtree on the wrong side breaks order.
#[test]
fn test_vt_tier60f_wrong_subtree_side_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30, 25]);

    ctx.push_assert("wrong_side", "key_post.index(3) < key_post.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 60f SOUNDNESS: wrong subtree side must be rejected, got: {:?}",
        result,
    );
}
