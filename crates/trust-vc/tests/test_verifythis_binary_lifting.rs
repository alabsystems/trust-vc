// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 82 - Binary Lifting / Lowest Common Ancestor VCs.
//!
//! Binary lifting precomputes `up[k][v]`, the `2^k`-th ancestor of node `v`.
//! Lowest-common-ancestor queries then follow three proof steps:
//!   1. the base parent table and doubled ancestor tables agree
//!   2. the deeper node is lifted until both nodes have the same depth
//!   3. if the aligned nodes still differ, lift both upward until their parents
//!      coincide; that parent is the LCA
//!
//! Concrete 8-node rooted tree used below:
//!
//!   0
//!   |- 1
//!   |  |- 3
//!   |  `- 4
//!   |     `- 7
//!   `- 2
//!      |- 5
//!      `- 6
//!
//! Depths: [0, 1, 1, 2, 2, 2, 2, 3]
//! up0   : [0, 0, 0, 1, 1, 2, 2, 4]
//! up1   : [0, 0, 0, 0, 0, 0, 0, 1]
//! up2   : [0, 0, 0, 0, 0, 0, 0, 0]
//!
//! 11 tests: 8 positive (table semantics, lifting, LCA cases)
//!         + 3 negatives (wrong lift, wrong equality, wrong LCA).
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

fn assume_seq_u64(ctx: &mut VerificationContext, name: &str, values: &[u64]) {
    ctx.declare_var_parsed(name, "Seq<u64>");
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

fn assume_binary_lifting_tree(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "depth", &[0, 1, 1, 2, 2, 2, 2, 3]);
    assume_seq_u64(ctx, "up0", &[0, 0, 0, 1, 1, 2, 2, 4]);
    assume_seq_u64(ctx, "up1", &[0, 0, 0, 0, 0, 0, 0, 1]);
    assume_seq_u64(ctx, "up2", &[0, 0, 0, 0, 0, 0, 0, 0]);
}

// ========================================================================
// GROUP A: Parent table and doubling semantics
// ========================================================================

/// Tier 82a: the base parent table and depths match the rooted tree.
#[test]
fn test_vt_tier82a_parent_and_depth_tables_match_tree() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.push_assert("root_depth", "depth.index(0) == 0");
    ctx.push_assert("root_self_parent", "up0.index(0) == 0");
    ctx.push_assert("node3_parent", "up0.index(3) == 1");
    ctx.push_assert("node5_parent", "up0.index(5) == 2");
    ctx.push_assert("node7_parent", "up0.index(7) == 4");
    ctx.push_assert("node4_depth", "depth.index(4) == 2");
    ctx.push_assert("node7_depth", "depth.index(7) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82a: parent/depth tables should verify, got: {:?}",
        result,
    );
}

/// Tier 82a: `up1` stores the two-step ancestor `up0[up0[v]]`.
#[test]
fn test_vt_tier82a_up1_matches_two_step_ancestor_recurrence() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.push_assert(
        "node3_up1_recurrence",
        "up1.index(3) == up0.index(up0.index(3))",
    );
    ctx.push_assert(
        "node7_up1_recurrence",
        "up1.index(7) == up0.index(up0.index(7))",
    );
    ctx.push_assert("node3_up1_value", "up1.index(3) == 0");
    ctx.push_assert("node7_up1_value", "up1.index(7) == 1");
    ctx.push_assert("node5_up1_value", "up1.index(5) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82a: two-step ancestor table should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Lifting and depth alignment
// ========================================================================

/// Tier 82b: lifting node 7 by 1, 2, and 3 levels yields 4, 1, and 0.
#[test]
fn test_vt_tier82b_lifting_node_seven_by_one_two_and_three_steps() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("lift1", "u64");
    ctx.declare_var_parsed("lift2", "u64");
    ctx.declare_var_parsed("lift3", "u64");

    ctx.push_assume("lift1_def", "lift1 == up0.index(7)");
    ctx.push_assume("lift2_def", "lift2 == up1.index(7)");
    ctx.push_assume("lift3_def", "lift3 == up0.index(up1.index(7))");

    ctx.push_assert("lift1_value", "lift1 == 4");
    ctx.push_assert("lift2_value", "lift2 == 1");
    ctx.push_assert("lift3_value", "lift3 == 0");
    ctx.push_assert(
        "lift_chain_strictly_moves",
        "lift1 != lift2 && lift2 != lift3",
    );
    ctx.push_assert("lift2_matches_table", "lift2 == up0.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82b: lifting node 7 should verify, got: {:?}",
        result,
    );
}

/// Tier 82b: before comparing nodes 7 and 3, lift 7 once so both sit at depth 2.
#[test]
fn test_vt_tier82b_aligns_deeper_node_before_same_depth_compare() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("u", "u64");
    ctx.declare_var_parsed("v", "u64");
    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.declare_var_parsed("aligned_v", "u64");

    ctx.push_assume("u_val", "u == 7");
    ctx.push_assume("v_val", "v == 3");
    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(u)");
    ctx.push_assume("aligned_v_def", "aligned_v == v");

    ctx.push_assert("original_depth_gap", "depth.index(7) == depth.index(3) + 1");
    ctx.push_assert("aligned_u_value", "aligned_u == 4");
    ctx.push_assert("aligned_v_value", "aligned_v == 3");
    ctx.push_assert(
        "depths_match_after_alignment",
        "depth.index(4) == depth.index(3)",
    );
    ctx.push_assert("aligned_nodes_still_differ", "aligned_u != aligned_v");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82b: depth alignment before LCA should verify, got: {:?}",
        result,
    );
}

/// Tier 82b: when one node is already an ancestor, alignment returns that ancestor directly.
#[test]
fn test_vt_tier82b_descendant_query_returns_aligned_ancestor() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("u", "u64");
    ctx.declare_var_parsed("v", "u64");
    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.declare_var_parsed("lca", "u64");

    ctx.push_assume("u_val", "u == 7");
    ctx.push_assume("v_val", "v == 4");
    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(u)");
    ctx.push_assume("lca_def", "lca == aligned_u");

    ctx.push_assert("depth_gap_one", "depth.index(7) == depth.index(4) + 1");
    ctx.push_assert("aligned_hits_ancestor", "aligned_u == v");
    ctx.push_assert("lca_value", "lca == 4");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82b: descendant query should return the aligned ancestor, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Lowest common ancestor outcomes
// ========================================================================

/// Tier 82c: siblings 5 and 6 share parent 2 as their LCA.
#[test]
fn test_vt_tier82c_sibling_query_returns_parent() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("u", "u64");
    ctx.declare_var_parsed("v", "u64");
    ctx.declare_var_parsed("lca", "u64");

    ctx.push_assume("u_val", "u == 5");
    ctx.push_assume("v_val", "v == 6");
    ctx.push_assume("lca_def", "lca == up0.index(u)");

    ctx.push_assert("same_depth", "depth.index(5) == depth.index(6)");
    ctx.push_assert("shared_parent", "up0.index(6) == lca");
    ctx.push_assert("lca_value", "lca == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82c: sibling LCA should verify, got: {:?}",
        result,
    );
}

/// Tier 82c: nodes 7 and 3 meet at internal ancestor 1 after aligning 7 to node 4.
#[test]
fn test_vt_tier82c_branch_query_returns_internal_ancestor() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.declare_var_parsed("jump_u", "u64");
    ctx.declare_var_parsed("jump_v", "u64");
    ctx.declare_var_parsed("lca", "u64");

    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(7)");
    ctx.push_assume("jump_u_def", "jump_u == up0.index(aligned_u)");
    ctx.push_assume("jump_v_def", "jump_v == up0.index(3)");
    ctx.push_assume("lca_def", "lca == jump_u");

    ctx.push_assert("aligned_u_value", "aligned_u == 4");
    ctx.push_assert("jump_u_value", "jump_u == 1");
    ctx.push_assert("jump_v_value", "jump_v == 1");
    ctx.push_assert("jumps_meet", "jump_u == jump_v");
    ctx.push_assert("lca_value", "lca == 1");
    ctx.push_assert("lca_matches_two_step_lift", "lca == up1.index(7)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82c: internal-ancestor LCA should verify, got: {:?}",
        result,
    );
}

/// Tier 82c: nodes 7 and 5 diverge under parents 1 and 2, so their LCA is the root 0.
#[test]
fn test_vt_tier82c_cross_subtree_query_returns_root() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.declare_var_parsed("aligned_v", "u64");
    ctx.declare_var_parsed("jump_u", "u64");
    ctx.declare_var_parsed("jump_v", "u64");
    ctx.declare_var_parsed("lca", "u64");

    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(7)");
    ctx.push_assume("aligned_v_def", "aligned_v == 5");
    ctx.push_assume("jump_u_def", "jump_u == up0.index(aligned_u)");
    ctx.push_assume("jump_v_def", "jump_v == up0.index(aligned_v)");
    ctx.push_assume("lca_def", "lca == up0.index(jump_u)");

    ctx.push_assert("aligned_u_value", "aligned_u == 4");
    ctx.push_assert("aligned_v_value", "aligned_v == 5");
    ctx.push_assert(
        "equal_depth_after_alignment",
        "depth.index(4) == depth.index(5)",
    );
    ctx.push_assert("up1_coincides_at_root", "up1.index(4) == up1.index(5)");
    ctx.push_assert("jump_u_value", "jump_u == 1");
    ctx.push_assert("jump_v_value", "jump_v == 2");
    ctx.push_assert("parents_still_differ", "jump_u != jump_v");
    ctx.push_assert("lca_value", "lca == 0");
    ctx.push_assert("root_reached_from_both_sides", "lca == up0.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 82c: cross-subtree LCA should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 82d NEGATIVE: lifting node 7 by two levels does not reach the root.
#[test]
fn test_vt_tier82d_wrong_two_step_lift_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.push_assert("wrong_two_step_lift", "up1.index(7) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 82d SOUNDNESS: wrong two-step lift must be rejected, got: {:?}",
        result,
    );
}

/// Tier 82d NEGATIVE: equal depth after alignment does not mean the nodes are equal.
#[test]
fn test_vt_tier82d_equal_depth_does_not_imply_equal_nodes() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(7)");

    ctx.push_assert("wrong_aligned_equality", "aligned_u == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 82d SOUNDNESS: aligned nodes need not coincide, got: {:?}",
        result,
    );
}

/// Tier 82d NEGATIVE: nodes 7 and 5 do not have LCA 1; their LCA is the root.
#[test]
fn test_vt_tier82d_wrong_cross_subtree_lca_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_binary_lifting_tree(&mut ctx);

    ctx.declare_var_parsed("aligned_u", "u64");
    ctx.declare_var_parsed("jump_u", "u64");
    ctx.declare_var_parsed("lca", "u64");

    ctx.push_assume("aligned_u_def", "aligned_u == up0.index(7)");
    ctx.push_assume("jump_u_def", "jump_u == up0.index(aligned_u)");
    ctx.push_assume("lca_def", "lca == up0.index(jump_u)");

    ctx.push_assert("wrong_lca_value", "lca == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 82d SOUNDNESS: wrong cross-subtree LCA must be rejected, got: {:?}",
        result,
    );
}
