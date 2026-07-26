// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 84 - Tarjan Strongly Connected Components VCs.
//!
//! Tarjan's SCC algorithm is a competition-realistic graph pattern: it mixes
//! DFS discovery order, stack discipline, back-edge reasoning, lowlink
//! propagation, and component extraction.
//!
//! We model a 5-node graph in CSR form:
//!   - `row_starts = [0, 1, 2, 4, 5, 6]`
//!   - `edges = [1, 2, 0, 3, 4, 3]`
//!   - SCCs are `{0,1,2}` and `{3,4}`
//!
//! The key proof obligations are:
//!   1. discovery sets `disc[v] == low[v]` and pushes `v` on the stack
//!   2. tree-edge discovery preserves the ancestor stack prefix
//!   3. a back edge lowers `low[v]` to an ancestor discovery time
//!   4. returning from a child propagates the minimum lowlink upward
//!   5. `low[root] == disc[root]` triggers an SCC pop that clears `on_stack`
//!
//! 11 tests: 8 positive (discovery, lowlink, pop, full partition)
//!         + 3 negatives (missed back edge, premature root, incomplete pop).
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

fn assume_tarjan_graph(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "row_starts", &[0, 1, 2, 4, 5, 6]);
    assume_seq_u64(ctx, "edges", &[1, 2, 0, 3, 4, 3]);
}

// ========================================================================
// GROUP A: Discovery and stack growth
// ========================================================================

/// Tier 84a: visiting the root initializes matching discovery and lowlink.
#[test]
fn test_vt_tier84a_root_visit_sets_disc_low_and_stack_membership() {
    let mut ctx = VerificationContext::new();

    assume_seq_u64(&mut ctx, "stack", &[0, 0, 0, 0, 0]);
    assume_seq_u64(&mut ctx, "disc", &[0, 9, 9, 9, 9]);
    assume_seq_u64(&mut ctx, "low", &[0, 9, 9, 9, 9]);
    assume_seq_u64(&mut ctx, "on_stack", &[1, 0, 0, 0, 0]);

    ctx.push_assert("root_is_zero", "stack.index(0) == 0");
    ctx.push_assert(
        "root_disc_matches_low",
        "disc.index(stack.index(0)) == low.index(stack.index(0))",
    );
    ctx.push_assert("root_disc_zero", "disc.index(0) == 0");
    ctx.push_assert(
        "root_marked_on_stack",
        "on_stack.index(stack.index(0)) == 1",
    );
    ctx.push_assert(
        "others_not_on_stack",
        "on_stack.index(1) + on_stack.index(2) + on_stack.index(3) + on_stack.index(4) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84a: root visit should verify, got: {:?}",
        result,
    );
}

/// Tier 84a: discovering node 1 from root 0 preserves the stack prefix.
#[test]
fn test_vt_tier84a_tree_edge_pushes_child_and_preserves_prefix() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "stack", &[0]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 9, 9, 9]);
    assume_seq_u64(&mut ctx, "low", &[0, 1, 9, 9, 9]);
    assume_seq_u64(&mut ctx, "on_stack", &[1, 1, 0, 0, 0]);

    ctx.push_assert(
        "child_matches_first_edge",
        "stack_new.index(1) == edges.index(row_starts.index(0))",
    );
    ctx.push_assert(
        "prefix_root_preserved",
        "stack_new.index(0) == stack.index(0)",
    );
    ctx.push_assert(
        "child_discovered_after_root",
        "disc.index(stack_new.index(1)) > disc.index(stack.index(0))",
    );
    ctx.push_assert(
        "child_disc_matches_low",
        "disc.index(stack_new.index(1)) == low.index(stack_new.index(1))",
    );
    ctx.push_assert(
        "child_marked_on_stack",
        "on_stack.index(stack_new.index(1)) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84a: child discovery should verify, got: {:?}",
        result,
    );
}

/// Tier 84a: discovering node 2 from node 1 keeps the ancestor prefix intact.
#[test]
fn test_vt_tier84a_nested_discovery_keeps_ancestor_prefix() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "stack", &[0, 1]);
    assume_seq_u64(&mut ctx, "stack_new", &[0, 1, 2]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 9, 9]);
    assume_seq_u64(&mut ctx, "low", &[0, 1, 2, 9, 9]);
    assume_seq_u64(&mut ctx, "on_stack", &[1, 1, 1, 0, 0]);

    ctx.push_assert(
        "child_matches_second_edge",
        "stack_new.index(2) == edges.index(row_starts.index(1))",
    );
    ctx.push_assert("prefix_root", "stack_new.index(0) == stack.index(0)");
    ctx.push_assert("prefix_parent", "stack_new.index(1) == stack.index(1)");
    ctx.push_assert(
        "new_child_disc_matches_low",
        "disc.index(stack_new.index(2)) == low.index(stack_new.index(2))",
    );
    ctx.push_assert(
        "new_child_on_stack",
        "on_stack.index(stack_new.index(2)) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84a: nested discovery should preserve the prefix, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Back edges and lowlink propagation
// ========================================================================

/// Tier 84b: node 2's back edge to node 0 lowers its lowlink to the root's discovery time.
#[test]
fn test_vt_tier84b_back_edge_lowers_lowlink_to_ancestor_disc() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 9, 9]);
    assume_seq_u64(&mut ctx, "low", &[0, 1, 0, 9, 9]);
    assume_seq_u64(&mut ctx, "on_stack", &[1, 1, 1, 0, 0]);

    ctx.push_assert(
        "first_edge_of_two_is_root",
        "edges.index(row_starts.index(2)) == 0",
    );
    ctx.push_assert("back_edge_target_still_on_stack", "on_stack.index(0) == 1");
    ctx.push_assert(
        "lowlink_uses_ancestor_disc",
        "low.index(2) == disc.index(edges.index(row_starts.index(2)))",
    );
    ctx.push_assert("lowlink_strictly_drops", "low.index(2) < disc.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84b: back edge should lower lowlink, got: {:?}",
        result,
    );
}

/// Tier 84b: returning from node 2 propagates the minimum lowlink to node 1.
#[test]
fn test_vt_tier84b_return_from_child_propagates_minimum_lowlink() {
    let mut ctx = VerificationContext::new();

    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "low", &[0, 0, 0, 3, 3]);

    ctx.push_assert("child_and_parent_share_low", "low.index(1) == low.index(2)");
    ctx.push_assert("parent_low_hits_root", "low.index(1) == disc.index(0)");
    ctx.push_assert(
        "propagated_low_below_parent_disc",
        "low.index(1) < disc.index(1)",
    );
    ctx.push_assert(
        "root_cycle_collapses_three_nodes",
        "low.index(0) == low.index(1) && low.index(1) == low.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84b: child return should propagate the minimum lowlink, got: {:?}",
        result,
    );
}

/// Tier 84b: the 3<->4 cycle produces a two-node SCC rooted at node 3.
#[test]
fn test_vt_tier84b_two_node_cycle_shares_root_lowlink() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "low", &[0, 0, 0, 3, 3]);
    assume_seq_u64(&mut ctx, "on_stack", &[1, 1, 1, 1, 1]);

    ctx.push_assert(
        "edge_four_points_back_to_three",
        "edges.index(row_starts.index(4)) == 3",
    );
    ctx.push_assert("back_target_on_stack", "on_stack.index(3) == 1");
    ctx.push_assert("four_low_is_three_disc", "low.index(4) == disc.index(3)");
    ctx.push_assert("three_and_four_share_root", "low.index(3) == low.index(4)");
    ctx.push_assert("three_is_component_root", "low.index(3) == disc.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84b: two-node cycle lowlink should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: SCC extraction
// ========================================================================

/// Tier 84c: when node 3 becomes an SCC root, popping removes exactly nodes 4 and 3.
#[test]
fn test_vt_tier84c_root_criterion_pops_two_node_component() {
    let mut ctx = VerificationContext::new();

    assume_seq_u64(&mut ctx, "stack", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "stack_after", &[0, 1, 2]);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "low", &[0, 0, 0, 3, 3]);
    assume_seq_u64(&mut ctx, "on_stack_after", &[1, 1, 1, 0, 0]);
    assume_seq_u64(&mut ctx, "component", &[4, 3]);

    ctx.push_assert("root_criterion_holds", "low.index(3) == disc.index(3)");
    ctx.push_assert(
        "prefix_root_preserved",
        "stack_after.index(0) == stack.index(0)",
    );
    ctx.push_assert(
        "prefix_one_preserved",
        "stack_after.index(1) == stack.index(1)",
    );
    ctx.push_assert(
        "prefix_two_preserved",
        "stack_after.index(2) == stack.index(2)",
    );
    ctx.push_assert(
        "pop_order_starts_at_top",
        "component.index(0) == stack.index(4)",
    );
    ctx.push_assert("root_popped_last", "component.index(1) == stack.index(3)");
    ctx.push_assert(
        "popped_nodes_cleared",
        "on_stack_after.index(3) + on_stack_after.index(4) == 0",
    );
    ctx.push_assert(
        "earlier_cycle_remains_active",
        "on_stack_after.index(0) + on_stack_after.index(1) + on_stack_after.index(2) == 3",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84c: SCC pop should verify, got: {:?}",
        result,
    );
}

/// Tier 84c: the full trace partitions the graph into SCC roots 0 and 3.
#[test]
fn test_vt_tier84c_full_trace_partitions_graph_into_two_sccs() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "low", &[0, 0, 0, 3, 3]);
    assume_seq_u64(&mut ctx, "comp_root", &[0, 0, 0, 3, 3]);

    ctx.push_assert(
        "first_cycle_same_component",
        "comp_root.index(0) == comp_root.index(1) && comp_root.index(1) == comp_root.index(2)",
    );
    ctx.push_assert(
        "second_cycle_same_component",
        "comp_root.index(3) == comp_root.index(4)",
    );
    ctx.push_assert(
        "cross_edge_does_not_merge_components",
        "comp_root.index(2) != comp_root.index(3)",
    );
    ctx.push_assert(
        "first_component_uses_root_zero",
        "comp_root.index(2) == low.index(2)",
    );
    ctx.push_assert(
        "second_component_uses_root_three",
        "comp_root.index(4) == low.index(4)",
    );
    ctx.push_assert(
        "tail_cycle_stays_below_root_cycle",
        "low.index(3) > disc.index(2)",
    );
    ctx.push_assert(
        "edge_to_tail_points_into_later_component",
        "edges.index(row_starts.index(2) + 1) == 3",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 84c: full Tarjan trace should partition SCCs, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 84d NEGATIVE: ignoring node 2's back edge leaves an unsound lowlink.
#[test]
fn test_vt_tier84d_missing_back_edge_update_rejected() {
    let mut ctx = VerificationContext::new();

    assume_tarjan_graph(&mut ctx);
    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 9, 9]);
    assume_seq_u64(&mut ctx, "low", &[0, 1, 2, 9, 9]);

    ctx.push_assert(
        "wrongly_claim_low_tracks_back_edge",
        "low.index(2) == disc.index(edges.index(row_starts.index(2)))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 84d SOUNDNESS: missing back-edge update must be rejected, got: {:?}",
        result,
    );
}

/// Tier 84d NEGATIVE: node 1 is not an SCC root because its lowlink points to node 0.
#[test]
fn test_vt_tier84d_non_root_vertex_must_not_trigger_component_pop() {
    let mut ctx = VerificationContext::new();

    assume_seq_u64(&mut ctx, "disc", &[0, 1, 2, 3, 4]);
    assume_seq_u64(&mut ctx, "low", &[0, 0, 0, 3, 3]);

    ctx.push_assert("wrong_root_claim", "low.index(1) == disc.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 84d SOUNDNESS: non-root vertex must not pop an SCC, got: {:?}",
        result,
    );
}

/// Tier 84d NEGATIVE: popping the {3,4} SCC must clear both `on_stack` bits.
#[test]
fn test_vt_tier84d_component_pop_must_clear_all_popped_nodes() {
    let mut ctx = VerificationContext::new();

    assume_seq_u64(&mut ctx, "on_stack_after", &[1, 1, 1, 1, 0]);

    ctx.push_assert(
        "all_popped_nodes_cleared",
        "on_stack_after.index(3) + on_stack_after.index(4) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 84d SOUNDNESS: incomplete SCC pop must be rejected, got: {:?}",
        result,
    );
}
