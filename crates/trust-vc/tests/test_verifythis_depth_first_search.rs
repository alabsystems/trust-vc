// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 53 - Depth-First Search (DFS) graph traversal VCs.
//!
//! Depth-first search appears in VerifyThis-style graph tasks, tree traversals,
//! work-stealing variants, and cycle-detection problems. We model:
//!   - `row_starts: Seq<u64>` and `edges: Seq<u64>` as CSR adjacency
//!   - `stack: Seq<u64>` as the explicit DFS frontier
//!   - `parent: Seq<u64>` and `depth: Seq<u64>` for tree structure
//!   - `disc: Seq<u64>` and `finish: Seq<u64>` for discovery/finish order
//!   - `color: Seq<u64>` where 0=white, 1=gray, 2=black
//!
//! Core proof obligations:
//!   1. init seeds the root and colors it gray
//!   2. discovery pushes a neighbor and sets parent/depth/discovery
//!   3. backtracking pops the finished leaf while preserving ancestors
//!   4. finish times respect child-before-parent ordering
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

// ========================================================================
// GROUP A: Init and discovery
// ========================================================================

/// Tier 53a: DFS init pushes the root and colors it gray.
#[test]
fn test_vt_tier53a_dfs_init_marks_root_gray() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "stack", &[0, 0, 0, 0]);
    assume_seq_u64(&mut ctx, "disc", &[0, 9, 9, 9]);
    assume_seq_u64(&mut ctx, "depth", &[0, 0, 0, 0]);
    assume_seq_u64(&mut ctx, "color", &[1, 0, 0, 0]);

    ctx.push_assert("root_in_bounds", "stack.index(0) < color.len()");
    ctx.push_assert(
        "root_disc_matches_depth",
        "disc.index(stack.index(0)) == depth.index(stack.index(0))",
    );
    ctx.push_assert("root_gray", "color.index(stack.index(0)) == 1");
    ctx.push_assert(
        "others_white",
        "color.index(1) + color.index(2) + color.index(3) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 53a: DFS init should seed the gray root, got: {:?}",
        result,
    );
}

/// Tier 53b: discovering the first child pushes the first outgoing edge.
#[test]
fn test_vt_tier53b_discover_first_child_pushes_neighbor() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 3, 3, 3]);
    assume_seq_u64(&mut ctx, "edges", &[1, 2, 3]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1, 0, 0]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 9, 9]);
    assume_seq_u64(&mut ctx, "depth", &[0, 1, 0, 0]);
    assume_seq_u64(&mut ctx, "parent", &[0, 0, 0, 0]);

    ctx.push_assert(
        "child_matches_first_edge",
        "stack_new.index(1) == edges.index(row_starts.index(0))",
    );
    ctx.push_assert(
        "depth_increases_by_one",
        "depth.index(stack_new.index(1)) == depth.index(stack_new.index(0)) + 1",
    );
    ctx.push_assert(
        "discovery_order_increases",
        "disc.index(stack_new.index(1)) > disc.index(stack_new.index(0))",
    );
    ctx.push_assert(
        "parent_points_to_root",
        "parent.index(stack_new.index(1)) == stack_new.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 53b: DFS child discovery should verify, got: {:?}",
        result,
    );
}

/// Tier 53c: discovering a grandchild preserves the ancestor stack prefix.
#[test]
fn test_vt_tier53c_second_discovery_preserves_prefix() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 3, 3, 3]);
    assume_seq_u64(&mut ctx, "edges", &[1, 2, 3]);
    assume_seq_u64(&mut ctx, "stack", &[0, 1]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1, 3]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 9, 2]);
    assume_seq_u64(&mut ctx, "depth", &[0, 1, 0, 2]);
    assume_seq_u64(&mut ctx, "parent", &[0, 0, 0, 1]);

    ctx.push_assert(
        "grandchild_matches_edge",
        "stack_new.index(2) == edges.index(row_starts.index(1))",
    );
    ctx.push_assert(
        "prefix_root_preserved",
        "stack_new.index(0) == stack.index(0)",
    );
    ctx.push_assert(
        "prefix_parent_preserved",
        "stack_new.index(1) == stack.index(1)",
    );
    ctx.push_assert(
        "grandchild_depth",
        "depth.index(stack_new.index(2)) == depth.index(stack.index(1)) + 1",
    );
    ctx.push_assert(
        "grandchild_parent",
        "parent.index(stack_new.index(2)) == stack.index(1)",
    );
    ctx.push_assert(
        "grandchild_discovered_after_parent",
        "disc.index(stack_new.index(2)) > disc.index(stack.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 53c: deeper DFS discovery should preserve the ancestor prefix, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Backtracking and finish order
// ========================================================================

/// Tier 53d: finishing a leaf pops it while keeping the ancestor prefix intact.
#[test]
fn test_vt_tier53d_finish_leaf_pops_stack_and_preserves_ancestors() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "stack", &[0, 1, 3]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1]);
    assume_seq_u64(&mut ctx, "finish", &[7, 4, 0, 3]);
    assume_seq_u64(&mut ctx, "color", &[1, 1, 0, 2]);

    ctx.push_assert(
        "prefix_root_preserved",
        "stack_new.index(0) == stack.index(0)",
    );
    ctx.push_assert(
        "prefix_parent_preserved",
        "stack_new.index(1) == stack.index(1)",
    );
    ctx.push_assert(
        "leaf_finishes_before_parent",
        "finish.index(stack.index(2)) < finish.index(stack_new.index(1))",
    );
    ctx.push_assert("leaf_black", "color.index(stack.index(2)) == 2");
    ctx.push_assert(
        "popped_leaf_removed",
        "stack.index(2) != stack_new.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 53d: DFS backtracking should verify, got: {:?}",
        result,
    );
}

/// Tier 53e: full DFS trace on 0->{1,2}, 1->{3} respects discovery and finish order.
#[test]
fn test_vt_tier53e_full_tree_trace_respects_dfs_ordering() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 3, 3, 3]);
    assume_seq_u64(&mut ctx, "edges", &[1, 2, 3]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 5, 2]);
    assume_seq_u64(&mut ctx, "finish", &[7, 4, 6, 3]);
    assume_seq_u64(&mut ctx, "depth", &[0, 1, 1, 2]);
    assume_seq_u64(&mut ctx, "parent", &[0, 0, 0, 1]);

    ctx.push_assert(
        "root_before_first_child",
        "disc.index(0) < disc.index(edges.index(0))",
    );
    ctx.push_assert(
        "grandchild_after_parent_discovery",
        "disc.index(edges.index(row_starts.index(1))) > disc.index(1)",
    );
    ctx.push_assert(
        "grandchild_finishes_before_parent",
        "finish.index(edges.index(row_starts.index(1))) < finish.index(1)",
    );
    ctx.push_assert(
        "child_finishes_before_root",
        "finish.index(1) < finish.index(0)",
    );
    ctx.push_assert(
        "sibling_finishes_before_root",
        "finish.index(2) < finish.index(0)",
    );
    ctx.push_assert(
        "grandchild_depth_matches_parent",
        "depth.index(edges.index(row_starts.index(1))) == depth.index(parent.index(edges.index(row_starts.index(1)))) + 1",
    );
    ctx.push_assert(
        "parent_discovered_first",
        "disc.index(parent.index(3)) < disc.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 53e: full DFS tree trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 53f: discovery must increase depth; keeping the same depth is unsound.
#[test]
fn test_vt_tier53f_wrong_child_depth_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 3, 3, 3]);
    assume_seq_u64(&mut ctx, "edges", &[1, 2, 3]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1, 0, 0]);
    assume_seq_u64(&mut ctx, "depth", &[0, 1, 0, 0]);

    ctx.push_assert(
        "wrong_same_depth",
        "depth.index(stack_new.index(1)) == depth.index(stack_new.index(0))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 53f SOUNDNESS: child discovery must reject the wrong depth, got: {:?}",
        result,
    );
}

/// Tier 53g: a parent cannot finish before its own grandchild.
#[test]
fn test_vt_tier53g_wrong_finish_order_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 3, 3, 3]);
    assume_seq_u64(&mut ctx, "edges", &[1, 2, 3]);
    assume_seq_u64(&mut ctx, "finish", &[7, 4, 6, 3]);
    assume_seq_u64(&mut ctx, "parent", &[0, 0, 0, 1]);

    ctx.push_assert(
        "wrong_parent_finishes_first",
        "finish.index(parent.index(edges.index(row_starts.index(1)))) < finish.index(edges.index(row_starts.index(1)))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 53g SOUNDNESS: DFS finish order must reject parent-before-child, got: {:?}",
        result,
    );
}
