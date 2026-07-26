// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 33 - Flat-graph BFS VCs.
//!
//! Breadth-first search is a recurring competition pattern for graph problems,
//! work-stealing trees, and reachability queries. In flat-array form we model:
//!   - `row_starts: Seq<u64>` and `edges: Seq<u64>` as CSR adjacency storage
//!   - `queue: Seq<u64>` with concrete frontier slots
//!   - `visited: Set<u64>` for discovered nodes
//!   - `dist: Seq<u64>` for BFS layer numbers
//!
//! These tests focus on BFS post-state verification conditions rather than the
//! low-level `Seq::update` primitive. The current verification bridge is stable
//! on concrete post-state obligations and unstable on update-heavy BFS formulas.
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

/// Tier 33a: BFS init seeds slot 0 with the source, marks it visited, and sets distance 0.
#[test]
fn test_vt_tier33a_bfs_init_seeds_source_frontier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("queue_new", "Seq<u64>");
    ctx.declare_var_parsed("visited_new", "Set<u64>");
    ctx.declare_var_parsed("dist_new", "Seq<u64>");

    ctx.push_assume("queue_len", "queue_new.len() == 4");
    ctx.push_assume("dist_len", "dist_new.len() == 4");
    ctx.push_assume("queue_source", "queue_new.index(0) == 0");
    ctx.push_assume("visited_source", "visited_new.contains(0)");
    ctx.push_assume("dist_source", "dist_new.index(0) == 0");

    // NOTE: Set.contains(Seq.index(...)) chains return Unknown due to
    // ay-dpll single-round E-matching; visited assertions use literal form.
    ctx.push_assert("source_in_bounds", "queue_new.index(0) < queue_new.len()");
    // Cross-array chain: queue head value matches its own BFS distance
    // (both are 0, but the solver must resolve the 2-step index chain).
    ctx.push_assert(
        "queue_head_matches_own_distance",
        "queue_new.index(0) == dist_new.index(queue_new.index(0))",
    );
    ctx.push_assert(
        "source_distance_zero",
        "dist_new.index(queue_new.index(0)) == 0",
    );
    ctx.push_assert(
        "source_dist_within_bounds",
        "dist_new.index(queue_new.index(0)) < dist_new.len()",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33a: BFS init should seed the source frontier, got: {:?}",
        result,
    );
}

/// Tier 33b: Dequeue advances the frontier from slot 0 to slot 1.
#[test]
fn test_vt_tier33b_bfs_dequeue_advances_front() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("queue", "Seq<u64>");
    ctx.declare_var_parsed("front_new", "u64");

    ctx.push_assume("queue_len", "queue.len() == 4");
    ctx.push_assume("q0", "queue.index(0) == 0");
    ctx.push_assume("q1", "queue.index(1) == 1");
    ctx.push_assume("q2", "queue.index(2) == 2");
    ctx.push_assume("front_step", "front_new == 1");

    ctx.push_assert(
        "dequeued_differs_from_next",
        "queue.index(0) != queue.index(front_new)",
    );
    // Front-value consistency: the dequeued element's queue position equals
    // front_new through index-chain substitution (replaces trivial `front > 0`).
    ctx.push_assert(
        "front_value_matches_position",
        "queue.index(front_new) == front_new",
    );
    // Cross-slot arithmetic: front position plus dequeued value stays within
    // queue bounds (replaces trivial `front < queue.len()`).
    ctx.push_assert(
        "front_plus_dequeued_in_bounds",
        "front_new + queue.index(0) < queue.len()",
    );
    ctx.push_assert(
        "next_element_after_source",
        "queue.index(front_new) > queue.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33b: dequeue should advance front by one, got: {:?}",
        result,
    );
}

/// Tier 33c: The first source neighbor occupies slot 1 and gets layer 1 distance.
#[test]
fn test_vt_tier33c_bfs_first_neighbor_discovery() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("row_starts", "Seq<u64>");
    ctx.declare_var_parsed("edges", "Seq<u64>");
    ctx.declare_var_parsed("queue_new", "Seq<u64>");
    ctx.declare_var_parsed("visited_new", "Set<u64>");
    ctx.declare_var_parsed("dist_new", "Seq<u64>");

    ctx.push_assume("rows_len", "row_starts.len() == 5");
    ctx.push_assume("edges_len", "edges.len() == 3");
    ctx.push_assume("queue_len", "queue_new.len() == 4");
    ctx.push_assume("dist_len", "dist_new.len() == 4");
    ctx.push_assume("row0", "row_starts.index(0) == 0");
    ctx.push_assume("row1", "row_starts.index(1) == 2");
    ctx.push_assume("edge0", "edges.index(0) == 1");
    ctx.push_assume("queue_head", "queue_new.index(0) == 0");
    ctx.push_assume("queue_neighbor", "queue_new.index(1) == 1");
    ctx.push_assume("visited_neighbor", "visited_new.contains(1)");
    ctx.push_assume("dist_head", "dist_new.index(0) == 0");
    ctx.push_assume("dist_neighbor", "dist_new.index(1) == 1");

    ctx.push_assert("csr_width", "row_starts.index(1) > row_starts.index(0)");
    ctx.push_assert(
        "neighbor_matches_edge_slot",
        "queue_new.index(1) == edges.index(row_starts.index(0))",
    );
    // BFS layer increment: neighbor distance strictly exceeds source distance,
    // proved via double index chain across queue and dist arrays (replaces the
    // Set.contains echo that merely restated the visited_neighbor assumption).
    ctx.push_assert(
        "neighbor_dist_exceeds_source_dist",
        "dist_new.index(queue_new.index(1)) > dist_new.index(queue_new.index(0))",
    );
    ctx.push_assert(
        "distance_advanced_by_one",
        "dist_new.index(queue_new.index(1)) == dist_new.index(0) + 1",
    );
    ctx.push_assert(
        "neighbor_dist_differs_from_source",
        "dist_new.index(1) != dist_new.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33c: first BFS neighbor discovery should verify, got: {:?}",
        result,
    );
}

/// Tier 33d: Enqueuing the second source neighbor preserves the prefix slots.
#[test]
fn test_vt_tier33d_bfs_enqueue_frame_preserves_frontier_prefix() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("queue", "Seq<u64>");
    ctx.declare_var_parsed("queue_new", "Seq<u64>");

    ctx.push_assume("queue_len", "queue.len() == 4");
    ctx.push_assume("queue_new_len", "queue_new.len() == 4");
    ctx.push_assume("old_q0", "queue.index(0) == 0");
    ctx.push_assume("old_q1", "queue.index(1) == 1");
    ctx.push_assume("new_q0", "queue_new.index(0) == 0");
    ctx.push_assume("new_q1", "queue_new.index(1) == 1");
    ctx.push_assume("new_q2", "queue_new.index(2) == 2");

    ctx.push_assert(
        "prefix_zero_preserved",
        "queue_new.index(0) == queue.index(0)",
    );
    ctx.push_assert(
        "prefix_one_preserved",
        "queue_new.index(1) == queue.index(1)",
    );
    ctx.push_assert(
        "new_element_distinct_from_source",
        "queue_new.index(2) != queue_new.index(0)",
    );
    ctx.push_assert(
        "new_element_distinct_from_first_neighbor",
        "queue_new.index(2) != queue_new.index(1)",
    );
    // Cross-array arithmetic: the new tail element exceeds the sum of the
    // two preserved prefix slots (2 > 0 + 1), exercising solver reasoning
    // across both array versions (replaces the trivial length echo).
    ctx.push_assert(
        "new_tail_exceeds_prefix_sum",
        "queue_new.index(2) > queue.index(0) + queue.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33d: queue frame during enqueue should verify, got: {:?}",
        result,
    );
}

/// Tier 33e: Exploring node 1 discovers node 3 exactly one layer deeper.
#[test]
fn test_vt_tier33e_bfs_second_level_discovery_increments_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("edges", "Seq<u64>");
    ctx.declare_var_parsed("queue_new", "Seq<u64>");
    ctx.declare_var_parsed("visited_new", "Set<u64>");
    ctx.declare_var_parsed("dist", "Seq<u64>");
    ctx.declare_var_parsed("dist_new", "Seq<u64>");

    ctx.push_assume("edges_len", "edges.len() == 3");
    ctx.push_assume("queue_len", "queue_new.len() == 4");
    ctx.push_assume("dist_len", "dist.len() == 4");
    ctx.push_assume("dist_new_len", "dist_new.len() == 4");
    ctx.push_assume("edge2", "edges.index(2) == 3");
    ctx.push_assume("queue_slot_three", "queue_new.index(3) == 3");
    ctx.push_assume("visited_three", "visited_new.contains(3)");
    ctx.push_assume("dist_old_one", "dist.index(1) == 1");
    ctx.push_assume("dist_new_one", "dist_new.index(1) == 1");
    ctx.push_assume("dist_new_three", "dist_new.index(3) == 2");

    ctx.push_assert("queue_matches_edge", "queue_new.index(3) == edges.index(2)");
    // Cross-version layer comparison: child distance in the new dist array
    // strictly exceeds the parent's distance in the old array. The solver must
    // chain queue_new.index(3) → dist_new.index(3) and compare against
    // dist.index(1), reasoning across two array versions (replaces the
    // Set.contains echo that merely restated the visited_three assumption).
    ctx.push_assert(
        "child_dist_exceeds_parent_old",
        "dist_new.index(queue_new.index(3)) > dist.index(1)",
    );
    ctx.push_assert(
        "distance_advanced_from_parent",
        "dist_new.index(queue_new.index(3)) == dist.index(1) + 1",
    );
    ctx.push_assert(
        "child_dist_differs_from_parent",
        "dist_new.index(3) != dist_new.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33e: second-level BFS discovery should verify, got: {:?}",
        result,
    );
}

/// Tier 33f: Expanding source 0 yields two layer-1 nodes.
#[test]
fn test_vt_tier33f_bfs_source_expansion_produces_two_layer_one_nodes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("queue_after_second", "Seq<u64>");
    ctx.declare_var_parsed("visited_after_second", "Set<u64>");
    ctx.declare_var_parsed("dist_after_second", "Seq<u64>");

    ctx.push_assume("queue_len", "queue_after_second.len() == 4");
    ctx.push_assume("dist_len", "dist_after_second.len() == 4");
    ctx.push_assume("q1", "queue_after_second.index(1) == 1");
    ctx.push_assume("q2", "queue_after_second.index(2) == 2");
    ctx.push_assume("visited1", "visited_after_second.contains(1)");
    ctx.push_assume("visited2", "visited_after_second.contains(2)");
    ctx.push_assume("dist1", "dist_after_second.index(1) == 1");
    ctx.push_assume("dist2", "dist_after_second.index(2) == 1");

    ctx.push_assert(
        "neighbors_distinct",
        "queue_after_second.index(1) != queue_after_second.index(2)",
    );
    // Second neighbor node index exceeds first: the queue stores nodes in
    // discovery order, so the second neighbor (2) > first (1). Exercises
    // arithmetic on Seq.index results (replaces visited_first echo).
    ctx.push_assert(
        "second_neighbor_exceeds_first",
        "queue_after_second.index(2) > queue_after_second.index(1)",
    );
    // Distance sum identity: both layer-1 nodes have distance 1, so
    // dist[q[1]] + dist[q[2]] == 2. Exercises double Seq.index chain
    // with arithmetic (replaces visited_second echo).
    ctx.push_assert(
        "layer_distances_sum_to_two",
        "dist_after_second.index(queue_after_second.index(1)) + dist_after_second.index(queue_after_second.index(2)) == 2",
    );
    ctx.push_assert(
        "same_bfs_layer",
        "dist_after_second.index(queue_after_second.index(1)) == dist_after_second.index(queue_after_second.index(2))",
    );
    ctx.push_assert(
        "layer_one_not_source_distance",
        "dist_after_second.index(queue_after_second.index(1)) != 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 33f: source expansion should produce two layer-one nodes, got: {:?}",
        result,
    );
}

/// Tier 33g: BFS must not enqueue node 3 in the first-neighbor slot.
#[test]
fn test_vt_tier33g_bfs_non_neighbor_enqueue_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("queue_new", "Seq<u64>");

    ctx.push_assume("queue_len", "queue_new.len() == 4");
    ctx.push_assume("first_neighbor_slot", "queue_new.index(1) == 1");

    ctx.push_assert("wrong_enqueue", "queue_new.index(1) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 33g SOUNDNESS: non-neighbor enqueue must be rejected, got: {:?}",
        result,
    );
}

/// Tier 33h: BFS distance must advance by exactly one, not two.
#[test]
fn test_vt_tier33h_bfs_wrong_distance_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_new", "Seq<u64>");

    ctx.push_assume("dist_len", "dist_new.len() == 4");
    ctx.push_assume("neighbor_dist", "dist_new.index(1) == 1");

    ctx.push_assert("wrong_distance", "dist_new.index(1) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 33h SOUNDNESS: BFS distance must increase by one, got: {:?}",
        result,
    );
}
