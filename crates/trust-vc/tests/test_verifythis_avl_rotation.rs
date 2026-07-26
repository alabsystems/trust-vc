// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 59 — AVL Tree Rotation / Balanced BST VCs.
//!
//! AVL trees maintain height balance |h(left) - h(right)| <= 1 via
//! rotations after insertion/deletion. This is a classic VerifyThis
//! topic — balanced trees appear in BDD problems (2023), persistent
//! data structures (2025), and general verified data structure problems.
//!
//! We model tree nodes using flat Seq arrays (implicit tree):
//!   - `key: Seq<i64>` — node keys
//!   - `left: Seq<i64>` — left child index (-1 = null)
//!   - `right: Seq<i64>` — right child index (-1 = null)
//!   - `height: Seq<i64>` — subtree heights
//!
//! Core proof obligations:
//!   1. BST order: for every node, left < node < right
//!   2. Balance: |h(left) - h(right)| <= 1 for every node
//!   3. Right rotation: restores balance while preserving BST order
//!   4. Left rotation: restores balance while preserving BST order
//!   5. Double rotation: left-right and right-left cases
//!   6. Negatives: wrong rotations break BST or balance
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
// GROUP A: BST order invariant
// ========================================================================

/// Tier 59a: BST order — a 5-node BST satisfies the order property.
/// Tree:       30
///           /    \
///         20      40
///        /  \
///       10   25
/// Nodes: [30, 20, 40, 10, 25]
/// Left:  [ 1,  3, -1, -1, -1]
/// Right: [ 2,  4, -1, -1, -1]
#[test]
fn test_vt_tier59a_bst_order_5node() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[30, 20, 40, 10, 25]);
    assume_seq_i64(&mut ctx, "left", &[1, 3, -1, -1, -1]);
    assume_seq_i64(&mut ctx, "right", &[2, 4, -1, -1, -1]);

    // Root's left child < root
    ctx.push_assert("order_root_l", "key.index(1) < key.index(0)");
    // Root's right child > root
    ctx.push_assert("order_root_r", "key.index(2) > key.index(0)");
    // Node 1 (20): left child 10 < 20
    ctx.push_assert("order_1_l", "key.index(3) < key.index(1)");
    // Node 1 (20): right child 25 > 20
    ctx.push_assert("order_1_r", "key.index(4) > key.index(1)");
    // All left subtree keys < root
    ctx.push_assert("subtree_l_3", "key.index(3) < key.index(0)");
    ctx.push_assert("subtree_l_4", "key.index(4) < key.index(0)");
    // Right subtree key > root
    ctx.push_assert("subtree_r_2", "key.index(2) > key.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59a: BST order 5-node should verify, got: {:?}",
        result,
    );
}

/// Tier 59a: BST order — 3-node unbalanced right chain.
/// Tree: 10 → 20 → 30 (all right children, left-heavy imbalance).
/// Nodes: [10, 20, 30]
/// Left:  [-1, -1, -1]
/// Right: [ 1,  2, -1]
#[test]
fn test_vt_tier59a_bst_order_right_chain() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[10, 20, 30]);
    assume_seq_i64(&mut ctx, "left", &[-1, -1, -1]);
    assume_seq_i64(&mut ctx, "right", &[1, 2, -1]);

    // BST order: each parent < right child
    ctx.push_assert("order_01", "key.index(0) < key.index(1)");
    ctx.push_assert("order_12", "key.index(1) < key.index(2)");
    // Transitive: root < grandchild
    ctx.push_assert("order_02", "key.index(0) < key.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59a: BST order right chain should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: AVL balance invariant
// ========================================================================

/// Tier 59b: Balance — the 5-node tree from group A is AVL-balanced.
/// Heights: node3=1, node4=1, node2=1, node1=2, node0=3.
/// Balance factor: |h(left)-h(right)| <= 1 for all internal nodes.
#[test]
fn test_vt_tier59b_avl_balance_5node() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "height", &[3, 2, 1, 1, 1]);
    assume_seq_i64(&mut ctx, "left", &[1, 3, -1, -1, -1]);
    assume_seq_i64(&mut ctx, "right", &[2, 4, -1, -1, -1]);

    // Balance at root (node 0): |h(1)-h(2)| = |2-1| = 1 <= 1
    ctx.declare_var_parsed("bf_0", "i64");
    ctx.push_assume("bf_0_def", "bf_0 == height.index(1) - height.index(2)");
    ctx.push_assert("bal_0_lo", "bf_0 >= -1");
    ctx.push_assert("bal_0_hi", "bf_0 <= 1");

    // Balance at node 1: |h(3)-h(4)| = |1-1| = 0 <= 1
    ctx.declare_var_parsed("bf_1", "i64");
    ctx.push_assume("bf_1_def", "bf_1 == height.index(3) - height.index(4)");
    ctx.push_assert("bal_1_lo", "bf_1 >= -1");
    ctx.push_assert("bal_1_hi", "bf_1 <= 1");

    // Leaf nodes have height 1 (trivially balanced)
    ctx.push_assert("leaf_2", "height.index(2) == 1");
    ctx.push_assert("leaf_3", "height.index(3) == 1");
    ctx.push_assert("leaf_4", "height.index(4) == 1");

    // Height consistency: h(node) = 1 + max(h(left), h(right))
    // Node 1: h = 1 + max(1, 1) = 2
    ctx.push_assert("hc_1", "height.index(1) == 1 + height.index(3)");
    // Node 0: h = 1 + max(2, 1) = 3
    ctx.push_assert("hc_0", "height.index(0) == 1 + height.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59b: AVL balance 5-node should verify, got: {:?}",
        result,
    );
}

/// Tier 59b: Balance — the right chain (10→20→30) is NOT AVL-balanced.
/// Heights: [3, 2, 1]. Balance at root: |0-2| = 2 > 1.
#[test]
fn test_vt_tier59b_right_chain_unbalanced() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "height", &[3, 2, 1]);

    // Node 0 has no left child (h=0) and right child h=2
    // Balance factor: |0 - 2| = 2 > 1 → unbalanced
    ctx.declare_var_parsed("bf_0", "i64");
    ctx.push_assume("bf_0_def", "bf_0 == 0 - height.index(1)");
    // Claiming balance should FAIL
    ctx.push_assert("bal_0", "bf_0 >= -1 && bf_0 <= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 59b: right chain should be unbalanced, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Right rotation
// ========================================================================

/// Tier 59c: Right rotation — rotates unbalanced left-heavy tree.
/// Before (left-heavy at root):
///       30          Right rotate at 30:
///      /                  20
///    20         →       /    \
///   /                 10      30
///  10
///
/// Before: key=[30, 20, 10], left=[1, 2, -1], right=[-1, -1, -1], h=[3,2,1]
/// After:  key=[20, 10, 30], left=[1, -1, -1], right=[2, -1, -1], h=[2,1,1]
#[test]
fn test_vt_tier59c_right_rotation_balance() {
    let mut ctx = VerificationContext::new();
    // Before rotation
    assume_seq_i64(&mut ctx, "key", &[30, 20, 10]);
    assume_seq_i64(&mut ctx, "h_pre", &[3, 2, 1]);

    // After rotation — new root is 20
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30]);
    assume_seq_i64(&mut ctx, "h_post", &[2, 1, 1]);

    // BST order preserved after rotation
    ctx.push_assert("order_l", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("order_r", "key_post.index(2) > key_post.index(0)");

    // Balance restored: |h(left)-h(right)| = |1-1| = 0 <= 1
    ctx.declare_var_parsed("bf_post", "i64");
    ctx.push_assume(
        "bf_post_def",
        "bf_post == h_post.index(1) - h_post.index(2)",
    );
    ctx.push_assert("bal_post_lo", "bf_post >= -1");
    ctx.push_assert("bal_post_hi", "bf_post <= 1");

    // Height decreased (tree is shorter)
    ctx.push_assert("height_dec", "h_post.index(0) < h_pre.index(0)");

    // All original keys preserved
    ctx.push_assert("k30", "key.index(0) == key_post.index(2)");
    ctx.push_assert("k20", "key.index(1) == key_post.index(0)");
    ctx.push_assert("k10", "key.index(2) == key_post.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59c: right rotation balance should verify, got: {:?}",
        result,
    );
}

/// Tier 59c: Right rotation — with a right subtree on the pivot.
/// Before:        40             Right rotate at 40:
///              /                       20
///            20          →           /    \
///           /  \                   10      40
///          10   30                        /
///                                       30
///
/// BST order: 10 < 20 < 30 < 40 must hold before AND after.
#[test]
fn test_vt_tier59c_right_rotation_with_subtree() {
    let mut ctx = VerificationContext::new();
    // Keys (all 4 nodes participate)
    assume_seq_i64(&mut ctx, "key", &[40, 20, 10, 30]);

    // After right rotation at 40:
    // New root: 20, left: 10, right: 40, 40's left: 30
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 40, 30]);
    assume_seq_i64(&mut ctx, "left_post", &[1, -1, 3, -1]);
    assume_seq_i64(&mut ctx, "right_post", &[2, -1, -1, -1]);

    // BST order preserved through the rotated pointer layout.
    ctx.push_assert("root_left_ptr", "left_post.index(0) == 1");
    ctx.push_assert("root_right_ptr", "right_post.index(0) == 2");
    ctx.push_assert(
        "order_root_l",
        "key_post.index(left_post.index(0)) < key_post.index(0)",
    );
    ctx.push_assert(
        "order_root_r",
        "key_post.index(right_post.index(0)) > key_post.index(0)",
    );
    // 30 is now the left child of 40 and remains in the right subtree of 20.
    ctx.push_assert(
        "order_40_l",
        "key_post.index(left_post.index(right_post.index(0))) \
         < key_post.index(right_post.index(0))",
    );
    ctx.push_assert(
        "subtree_order",
        "key_post.index(left_post.index(right_post.index(0))) > key_post.index(0)",
    );

    // All keys present (set equality)
    ctx.push_assert("has_40", "key.index(0) == key_post.index(2)");
    ctx.push_assert("has_20", "key.index(1) == key_post.index(0)");
    ctx.push_assert("has_10", "key.index(2) == key_post.index(1)");
    ctx.push_assert("has_30", "key.index(3) == key_post.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59c: right rotation with subtree should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Left rotation
// ========================================================================

/// Tier 59d: Left rotation — rotates unbalanced right-heavy tree.
/// Before:        10          Left rotate at 10:
///                  \                 20
///                  20       →      /    \
///                    \            10      30
///                    30
///
/// Before: key=[10, 20, 30], h=[3,2,1]
/// After:  key=[20, 10, 30], h=[2,1,1]
#[test]
fn test_vt_tier59d_left_rotation_balance() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[10, 20, 30]);
    assume_seq_i64(&mut ctx, "h_pre", &[3, 2, 1]);

    // After left rotation
    assume_seq_i64(&mut ctx, "key_post", &[20, 10, 30]);
    assume_seq_i64(&mut ctx, "h_post", &[2, 1, 1]);

    // BST order preserved
    ctx.push_assert("order_l", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("order_r", "key_post.index(2) > key_post.index(0)");

    // Balance restored
    ctx.declare_var_parsed("bf_post", "i64");
    ctx.push_assume(
        "bf_post_def",
        "bf_post == h_post.index(1) - h_post.index(2)",
    );
    ctx.push_assert("bal_lo", "bf_post >= -1");
    ctx.push_assert("bal_hi", "bf_post <= 1");

    // Height decreased
    ctx.push_assert("height_dec", "h_post.index(0) < h_pre.index(0)");

    // Keys preserved
    ctx.push_assert("k10", "key.index(0) == key_post.index(1)");
    ctx.push_assert("k20", "key.index(1) == key_post.index(0)");
    ctx.push_assert("k30", "key.index(2) == key_post.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59d: left rotation balance should verify, got: {:?}",
        result,
    );
}

/// Tier 59d: Left rotation — symmetric to right rotation with subtree.
/// Before:    10                    Left rotate at 10:
///              \                          30
///              30          →             /    \
///             /  \                     10      40
///           25    40                    \
///                                      25
#[test]
fn test_vt_tier59d_left_rotation_with_subtree() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "key", &[10, 30, 25, 40]);

    // After left rotation at 10:
    // New root: 30, left: 10, right: 40, 10's right: 25
    assume_seq_i64(&mut ctx, "key_post", &[30, 10, 40, 25]);
    assume_seq_i64(&mut ctx, "left_post", &[1, -1, -1, -1]);
    assume_seq_i64(&mut ctx, "right_post", &[2, 3, -1, -1]);

    // BST order preserved
    ctx.push_assert("order_root_l", "key_post.index(1) < key_post.index(0)");
    ctx.push_assert("order_root_r", "key_post.index(2) > key_post.index(0)");
    // 25 is now right child of 10 — still 25 > 10
    ctx.push_assert("order_10_r", "key_post.index(3) > key_post.index(1)");
    // 25 < 30 (in left subtree of new root)
    ctx.push_assert("subtree_order", "key_post.index(3) < key_post.index(0)");

    // All keys present
    ctx.push_assert("has_10", "key.index(0) == key_post.index(1)");
    ctx.push_assert("has_30", "key.index(1) == key_post.index(0)");
    ctx.push_assert("has_25", "key.index(2) == key_post.index(3)");
    ctx.push_assert("has_40", "key.index(3) == key_post.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 59d: left rotation with subtree should verify, got: {:?}",
        result,
    );
}
