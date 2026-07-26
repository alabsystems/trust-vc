// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 36 - Segment Tree / Range Query VCs.
//!
//! Segment trees are a standard competition data structure for interval sums,
//! point updates, and range queries. They appear whenever a VerifyThis-style
//! problem mixes mutable arrays with logarithmic query/update obligations.
//!
//! We model a size-4 sum segment tree as a flat `Seq<u64>` of length 7:
//!   - node 0: root covering [0, 4)
//!   - node 1: left child covering [0, 2)
//!   - node 2: right child covering [2, 4)
//!   - nodes 3..6: leaves covering the four singleton ranges
//!
//! The key proof obligations are local:
//!   - build: every internal node equals the sum of its two children
//!   - query: a range result is the sum of the disjoint nodes covering it
//!   - update: changing one leaf only affects the ancestor chain
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

// ========================================================================
// GROUP A: Build invariants on a concrete tree
// ========================================================================

/// Tier 36a: Concrete build for a = [2, 1, 3, 4].
/// Flat tree representation:
///   tree = [10, 3, 7, 2, 1, 3, 4]
/// where tree[0] = total sum, tree[1] = left half, tree[2] = right half.
#[test]
fn test_vt_tier36a_build_preserves_parent_sum_invariants() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");

    ctx.push_assume("len", "tree.len() == 7");
    ctx.push_assume("root", "tree.index(0) == 10");
    ctx.push_assume("left", "tree.index(1) == 3");
    ctx.push_assume("right", "tree.index(2) == 7");
    ctx.push_assume("leaf0", "tree.index(3) == 2");
    ctx.push_assume("leaf1", "tree.index(4) == 1");
    ctx.push_assume("leaf2", "tree.index(5) == 3");
    ctx.push_assume("leaf3", "tree.index(6) == 4");

    ctx.push_assert(
        "left_parent_sum",
        "tree.index(1) == tree.index(3) + tree.index(4)",
    );
    ctx.push_assert(
        "right_parent_sum",
        "tree.index(2) == tree.index(5) + tree.index(6)",
    );
    ctx.push_assert("root_sum", "tree.index(0) == tree.index(1) + tree.index(2)");
    ctx.push_assert(
        "root_matches_leaf_total",
        "tree.index(0) == tree.index(3) + tree.index(4) + tree.index(5) + tree.index(6)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36a: segment-tree build invariants should verify, got: {:?}",
        result,
    );
}

/// Tier 36b: Query [1, 3) decomposes into the two singleton leaves for
/// arr[1] and arr[2]. For a = [2, 1, 3, 4], the answer is 1 + 3 = 4.
#[test]
fn test_vt_tier36b_mid_range_query_decomposes_to_leaves() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");
    ctx.declare_var_parsed("query", "u64");

    ctx.push_assume("len", "tree.len() == 7");
    ctx.push_assume("root", "tree.index(0) == 10");
    ctx.push_assume("leaf0", "tree.index(3) == 2");
    ctx.push_assume("leaf1", "tree.index(4) == 1");
    ctx.push_assume("leaf2", "tree.index(5) == 3");
    ctx.push_assume("leaf3", "tree.index(6) == 4");
    ctx.push_assume("query_value", "query == tree.index(4) + tree.index(5)");

    ctx.push_assert(
        "query_is_root_without_outer_leaves",
        "query + tree.index(3) + tree.index(6) == tree.index(0)",
    );
    ctx.push_assert("query_exceeds_leaf1", "query > tree.index(4)");
    ctx.push_assert(
        "query_excludes_left_subtree_cover",
        "query != tree.index(3) + tree.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36b: middle range query should verify, got: {:?}",
        result,
    );
}

/// Tier 36c: Disjoint queries cover the full range.
/// Query [0, 2) is the left child, query [2, 4) is the right child,
/// and their sum equals the root.
#[test]
fn test_vt_tier36c_disjoint_queries_reconstruct_root() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");
    ctx.declare_var_parsed("left_sum", "u64");
    ctx.declare_var_parsed("right_sum", "u64");

    ctx.push_assume("len", "tree.len() == 7");
    ctx.push_assume("root", "tree.index(0) == 10");
    ctx.push_assume("left", "tree.index(1) == 3");
    ctx.push_assume("right", "tree.index(2) == 7");
    ctx.push_assume("leaf0", "tree.index(3) == 2");
    ctx.push_assume("leaf1", "tree.index(4) == 1");
    ctx.push_assume("leaf2", "tree.index(5) == 3");
    ctx.push_assume("leaf3", "tree.index(6) == 4");
    ctx.push_assume("left_query", "left_sum == tree.index(1)");
    ctx.push_assume("right_query", "right_sum == tree.index(2)");

    ctx.push_assert(
        "left_query_matches_left_cover",
        "left_sum == tree.index(3) + tree.index(4)",
    );
    ctx.push_assert(
        "right_query_matches_right_cover",
        "right_sum == tree.index(5) + tree.index(6)",
    );
    ctx.push_assert("cover_root", "left_sum + right_sum == tree.index(0)");
    ctx.push_assert("right_side_is_heavier", "right_sum > left_sum");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36c: disjoint range cover should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Point updates and ancestor propagation
// ========================================================================

/// Tier 36d: Point update at arr[1]: 1 -> 5.
/// Old tree: [10, 3, 7, 2, 1, 3, 4]
/// New tree: [14, 7, 7, 2, 5, 3, 4]
/// Only the updated leaf and its ancestors change.
#[test]
fn test_vt_tier36d_point_update_recomputes_ancestor_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");
    ctx.declare_var_parsed("tree_new", "Seq<u64>");

    ctx.push_assume("old_len", "tree.len() == 7");
    ctx.push_assume("new_len", "tree_new.len() == 7");
    ctx.push_assume("old_root", "tree.index(0) == 10");
    ctx.push_assume("old_left", "tree.index(1) == 3");
    ctx.push_assume("old_right", "tree.index(2) == 7");
    ctx.push_assume("old_leaf0", "tree.index(3) == 2");
    ctx.push_assume("old_leaf1", "tree.index(4) == 1");
    ctx.push_assume("old_leaf2", "tree.index(5) == 3");
    ctx.push_assume("old_leaf3", "tree.index(6) == 4");

    ctx.push_assume("new_root", "tree_new.index(0) == 14");
    ctx.push_assume("new_left", "tree_new.index(1) == 7");
    ctx.push_assume("new_right", "tree_new.index(2) == 7");
    ctx.push_assume("new_leaf0", "tree_new.index(3) == 2");
    ctx.push_assume("new_leaf1", "tree_new.index(4) == 5");
    ctx.push_assume("new_leaf2", "tree_new.index(5) == 3");
    ctx.push_assume("new_leaf3", "tree_new.index(6) == 4");

    ctx.push_assert(
        "updated_leaf_changes_value",
        "tree_new.index(4) != tree.index(4)",
    );
    ctx.push_assert(
        "left_recomputed",
        "tree_new.index(1) == tree_new.index(3) + tree_new.index(4)",
    );
    ctx.push_assert(
        "root_recomputed",
        "tree_new.index(0) == tree_new.index(1) + tree_new.index(2)",
    );
    ctx.push_assert("right_subtree_frame", "tree_new.index(2) == tree.index(2)");
    ctx.push_assert(
        "left_delta_matches_leaf_delta",
        "tree_new.index(1) + tree.index(4) == tree.index(1) + tree_new.index(4)",
    );
    ctx.push_assert(
        "root_delta_matches_leaf_delta",
        "tree_new.index(0) + tree.index(4) == tree.index(0) + tree_new.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36d: point update should propagate along ancestors, got: {:?}",
        result,
    );
}

/// Tier 36e: Updating the left half leaves the right subtree unchanged.
#[test]
fn test_vt_tier36e_point_update_preserves_disjoint_subtree() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");
    ctx.declare_var_parsed("tree_new", "Seq<u64>");

    ctx.push_assume("old_len", "tree.len() == 7");
    ctx.push_assume("new_len", "tree_new.len() == 7");
    ctx.push_assume("old_right", "tree.index(2) == 7");
    ctx.push_assume("old_leaf2", "tree.index(5) == 3");
    ctx.push_assume("old_leaf3", "tree.index(6) == 4");

    ctx.push_assume("new_right", "tree_new.index(2) == 7");
    ctx.push_assume("new_leaf2", "tree_new.index(5) == 3");
    ctx.push_assume("new_leaf3", "tree_new.index(6) == 4");

    ctx.push_assert("right_frame", "tree_new.index(2) == tree.index(2)");
    ctx.push_assert("leaf2_frame", "tree_new.index(5) == tree.index(5)");
    ctx.push_assert("leaf3_frame", "tree_new.index(6) == tree.index(6)");
    ctx.push_assert(
        "right_cover_still_matches_preserved_leaves",
        "tree_new.index(2) == tree_new.index(5) + tree_new.index(6)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36e: point update should preserve the disjoint subtree, got: {:?}",
        result,
    );
}

/// Tier 36f: Query [1, 4) on the updated tree combines the changed singleton
/// leaf [1, 2) with the untouched right child [2, 4).
#[test]
fn test_vt_tier36f_updated_suffix_query_uses_mixed_cover() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree_new", "Seq<u64>");
    ctx.declare_var_parsed("query", "u64");

    ctx.push_assume("len", "tree_new.len() == 7");
    ctx.push_assume("root", "tree_new.index(0) == 14");
    ctx.push_assume("left", "tree_new.index(1) == 7");
    ctx.push_assume("leaf0", "tree_new.index(3) == 2");
    ctx.push_assume("leaf1", "tree_new.index(4) == 5");
    ctx.push_assume("right", "tree_new.index(2) == 7");
    ctx.push_assume(
        "query_value",
        "query == tree_new.index(4) + tree_new.index(2)",
    );

    ctx.push_assert(
        "query_complements_excluded_prefix_leaf",
        "query + tree_new.index(3) == tree_new.index(0)",
    );
    ctx.push_assert(
        "query_matches_left_right_without_prefix_leaf",
        "query + tree_new.index(3) == tree_new.index(1) + tree_new.index(2)",
    );
    ctx.push_assert(
        "query_exceeds_untouched_right_cover",
        "query > tree_new.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 36f: updated suffix query should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 36g: A broken build that sets the root to 11 instead of 10 is wrong.
#[test]
fn test_vt_tier36g_wrong_root_sum_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");

    ctx.push_assume("len", "tree.len() == 7");
    ctx.push_assume("root", "tree.index(0) == 10");
    ctx.push_assume("left", "tree.index(1) == 3");
    ctx.push_assume("right", "tree.index(2) == 7");

    ctx.push_assert(
        "false_root",
        "tree.index(0) == tree.index(1) + tree.index(2) + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 36g SOUNDNESS: wrong root sum should be rejected, got: {:?}",
        result,
    );
}

/// Tier 36h: Updating the left subtree must not change the right range sum.
#[test]
fn test_vt_tier36h_false_cross_range_change_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tree", "Seq<u64>");
    ctx.declare_var_parsed("tree_new", "Seq<u64>");

    ctx.push_assume("old_len", "tree.len() == 7");
    ctx.push_assume("new_len", "tree_new.len() == 7");
    ctx.push_assume("old_right", "tree.index(2) == 7");
    ctx.push_assume("new_right", "tree_new.index(2) == 7");

    ctx.push_assert(
        "false_right_delta",
        "tree_new.index(2) == tree.index(2) + 4",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 36h SOUNDNESS: unrelated right range change should be rejected, got: {:?}",
        result,
    );
}
