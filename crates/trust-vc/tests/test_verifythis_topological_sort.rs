// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 35 — Topological Sort / DAG VCs.
//!
//! Topological sorting appears in VerifyThis-style tasks: task scheduling,
//! dependency resolution, work-stealing trees (2024), and build systems.
//! The core algorithm is Kahn's BFS-based topological sort:
//!   1. Compute in-degrees from adjacency structure
//!   2. Enqueue all nodes with in-degree 0
//!   3. Dequeue node u, append to output, decrement in-degree of neighbors
//!   4. If neighbor in-degree becomes 0, enqueue it
//!
//! We model the DAG as CSR-style adjacency (`edges: Seq<u64>`, `offsets: Seq<u64>`)
//! with `indeg: Seq<u64>` for in-degree tracking and `out: Seq<u64>` for the
//! output order. Cycle detection: if output length < node count, a cycle exists.
//!
//! KEY LESSON: Topological sort correctness requires two properties:
//!   1. Every edge (u,v) has u before v in the output (ordering)
//!   2. Every node appears exactly once (completeness)
//!      The ordering property reduces to checking `pos[u] < pos[v]` for each edge.
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
// GROUP A: In-degree computation and initial queue
// ========================================================================

/// Tier 35a: DAG with 4 nodes, edges 0→1, 0→2, 1→3, 2→3.
/// In-degrees: [0, 1, 1, 2]. A symbolic source variable must resolve to 0.
#[test]
fn test_vt_tier35a_indegree_computation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("indeg", "Seq<u64>");
    ctx.declare_var_parsed("src", "u64");

    ctx.push_assume("len", "indeg.len() == 4");
    ctx.push_assume("d0", "indeg.index(0) == 0");
    ctx.push_assume("d1", "indeg.index(1) == 1");
    ctx.push_assume("d2", "indeg.index(2) == 1");
    ctx.push_assume("d3", "indeg.index(3) == 2");

    // src is a valid index whose in-degree is 0
    ctx.push_assume("src_bound", "src < 4");
    ctx.push_assume("src_is_source", "indeg.index(src) == 0");

    // Derived: src must be node 0 — the only node with in-degree 0.
    // Requires the solver to check indeg[1]=1≠0, indeg[2]=1≠0, indeg[3]=2≠0.
    ctx.push_assert("source_uniqueness", "src == 0");
    // Sink in-degree equals the sum of the two middle-layer in-degrees.
    ctx.push_assert(
        "sink_collects_predecessors",
        "indeg.index(3) == indeg.index(1) + indeg.index(2)",
    );
    // Middle-layer nodes share the same in-degree (both receive one edge).
    ctx.push_assert("middle_layer_symmetric", "indeg.index(1) == indeg.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35a: in-degree computation should verify, got: {:?}",
        result,
    );
}

/// Tier 35b: After processing source node 0, in-degrees of neighbors
/// 1 and 2 decrement. Derive the exact decrement and total decrease.
#[test]
fn test_vt_tier35b_process_source_decrements_indegree() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("indeg", "Seq<u64>");
    ctx.declare_var_parsed("indeg_new", "Seq<u64>");

    ctx.push_assume("len", "indeg.len() == 4");
    ctx.push_assume("len_new", "indeg_new.len() == 4");
    // Before: indeg = [0, 1, 1, 2]
    ctx.push_assume("d0", "indeg.index(0) == 0");
    ctx.push_assume("d1", "indeg.index(1) == 1");
    ctx.push_assume("d2", "indeg.index(2) == 1");
    ctx.push_assume("d3", "indeg.index(3) == 2");

    // After processing node 0 (edges 0→1, 0→2): decrement indeg[1], indeg[2]
    ctx.push_assume("new_d0", "indeg_new.index(0) == 0");
    ctx.push_assume("new_d1", "indeg_new.index(1) == 0");
    ctx.push_assume("new_d2", "indeg_new.index(2) == 0");
    ctx.push_assume("new_d3", "indeg_new.index(3) == 2");

    // Decrement relationship: each neighbor's in-degree decreased by exactly 1.
    ctx.push_assert(
        "decrement_node1",
        "indeg_new.index(1) + 1 == indeg.index(1)",
    );
    ctx.push_assert(
        "decrement_node2",
        "indeg_new.index(2) + 1 == indeg.index(2)",
    );
    // Frame: non-neighbor retains old in-degree (cross-sequence equality).
    ctx.push_assert("frame_sink", "indeg_new.index(3) == indeg.index(3)");
    // Total in-degree decreased by exactly 2 (one per edge from the processed source).
    ctx.push_assert(
        "total_decrease",
        "indeg_new.index(0) + indeg_new.index(1) + indeg_new.index(2) + indeg_new.index(3) + 2 == indeg.index(0) + indeg.index(1) + indeg.index(2) + indeg.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35b: processing source should decrement neighbor in-degrees, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Output ordering property
// ========================================================================

/// Tier 35c: Full topological sort output for diamond DAG.
/// Edges: 0→1, 0→2, 1→3, 2→3. Valid output: [0, 1, 2, 3].
/// Verify edge ordering via nested pos[out[i]] == i (permutation inverse).
#[test]
fn test_vt_tier35c_output_respects_edge_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("out", "Seq<u64>");
    ctx.declare_var_parsed("pos", "Seq<u64>");

    ctx.push_assume("out_len", "out.len() == 4");
    ctx.push_assume("pos_len", "pos.len() == 4");
    // Output order: [0, 1, 2, 3]
    ctx.push_assume("out0", "out.index(0) == 0");
    ctx.push_assume("out1", "out.index(1) == 1");
    ctx.push_assume("out2", "out.index(2) == 2");
    ctx.push_assume("out3", "out.index(3) == 3");
    // Position array: pos[node] = index in output
    ctx.push_assume("pos0", "pos.index(0) == 0");
    ctx.push_assume("pos1", "pos.index(1) == 1");
    ctx.push_assume("pos2", "pos.index(2) == 2");
    ctx.push_assume("pos3", "pos.index(3) == 3");

    // Permutation inverse: pos[out[i]] == i (nested Seq index chain).
    ctx.push_assert("inverse_0", "pos.index(out.index(0)) == 0");
    ctx.push_assert("inverse_1", "pos.index(out.index(1)) == 1");
    ctx.push_assert("inverse_2", "pos.index(out.index(2)) == 2");
    ctx.push_assert("inverse_3", "pos.index(out.index(3)) == 3");
    // Transitive edge ordering: edge 0→1→3 implies pos[0] + 1 < pos[3].
    ctx.push_assert("transitive_chain_0_3", "pos.index(0) + 1 < pos.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35c: topological output should respect edge ordering, got: {:?}",
        result,
    );
}

/// Tier 35d: Alternative valid topological order [0, 2, 1, 3].
/// Both orderings are valid because 1 and 2 are independent.
/// Verify edge ordering via nested out[pos[node]] == node (inverse direction).
#[test]
fn test_vt_tier35d_alternative_valid_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("out", "Seq<u64>");
    ctx.declare_var_parsed("pos", "Seq<u64>");

    ctx.push_assume("out_len", "out.len() == 4");
    ctx.push_assume("pos_len", "pos.len() == 4");
    // Alternative order: [0, 2, 1, 3]
    ctx.push_assume("out0", "out.index(0) == 0");
    ctx.push_assume("out1", "out.index(1) == 2");
    ctx.push_assume("out2", "out.index(2) == 1");
    ctx.push_assume("out3", "out.index(3) == 3");
    // pos = [0, 2, 1, 3] (pos[node] = index in output)
    ctx.push_assume("pos0", "pos.index(0) == 0");
    ctx.push_assume("pos1", "pos.index(1) == 2");
    ctx.push_assume("pos2", "pos.index(2) == 1");
    ctx.push_assume("pos3", "pos.index(3) == 3");

    // Inverse: out[pos[node]] == node (nested Seq index chain).
    ctx.push_assert("out_pos_0", "out.index(pos.index(0)) == 0");
    ctx.push_assert("out_pos_1", "out.index(pos.index(1)) == 1");
    ctx.push_assert("out_pos_2", "out.index(pos.index(2)) == 2");
    ctx.push_assert("out_pos_3", "out.index(pos.index(3)) == 3");
    // Edge ordering through indirection: pos[out[0]] < pos[out[1]].
    // out[0]=0, out[1]=2 → pos[0]=0 < pos[2]=1.
    ctx.push_assert(
        "first_precedes_second",
        "pos.index(out.index(0)) < pos.index(out.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35d: alternative topological order should also verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Cycle detection
// ========================================================================

/// Tier 35e: Linear chain 0→1→2→3. Completeness verified through
/// nested output element lookup and symbolic last-position check.
#[test]
fn test_vt_tier35e_linear_chain_no_cycle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("out", "Seq<u64>");
    ctx.declare_var_parsed("pos", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("out_len", "out.len() == 4");
    ctx.push_assume("pos_len", "pos.len() == 4");
    ctx.push_assume("out0", "out.index(0) == 0");
    ctx.push_assume("out1", "out.index(1) == 1");
    ctx.push_assume("out2", "out.index(2) == 2");
    ctx.push_assume("out3", "out.index(3) == 3");
    ctx.push_assume("pos0", "pos.index(0) == 0");
    ctx.push_assume("pos1", "pos.index(1) == 1");
    ctx.push_assume("pos2", "pos.index(2) == 2");
    ctx.push_assume("pos3", "pos.index(3) == 3");

    // Completeness: output covers all n nodes.
    ctx.push_assert("complete", "out.len() == n");
    // The last output slot contains the terminal node of the chain.
    // Requires nested lookup: out[n-1] resolves to the chain's tail (3).
    ctx.push_assert("last_is_terminal", "pos.index(out.index(3)) + 1 == n");
    // Linear chain ordering: consecutive output positions differ by 1.
    ctx.push_assert(
        "consecutive_step",
        "pos.index(out.index(1)) == pos.index(out.index(0)) + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35e: linear chain should produce complete output, got: {:?}",
        result,
    );
}

/// Tier 35f: Cycle 0→1→2→0. All in-degrees positive means no source exists.
/// Derive cycle detection from the in-degree sum and output length relationship.
#[test]
fn test_vt_tier35f_cycle_detected_by_short_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("indeg", "Seq<u64>");
    ctx.declare_var_parsed("out_len", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_val", "n == 3");
    ctx.push_assume("indeg_len", "indeg.len() == 3");
    // Cycle: 0→1→2→0, all in-degrees == 1
    ctx.push_assume("d0", "indeg.index(0) == 1");
    ctx.push_assume("d1", "indeg.index(1) == 1");
    ctx.push_assume("d2", "indeg.index(2) == 1");
    // No source → Kahn's produces empty output
    ctx.push_assume("empty_output", "out_len == 0");

    // Cycle detection: output shorter than node count.
    ctx.push_assert("cycle_detected", "out_len < n");
    // The deficit equals the number of nodes trapped in cycles.
    ctx.push_assert("deficit_equals_cycle_size", "n == out_len + indeg.len()");
    // Every node contributes to the cycle: total in-degree == node count.
    ctx.push_assert(
        "total_indeg_equals_n",
        "indeg.index(0) + indeg.index(1) + indeg.index(2) == n",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 35f: cycle should be detected by short output, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 35g: Wrong ordering — placing 3 before 1 violates edge 1→3.
#[test]
fn test_vt_tier35g_wrong_order_violates_edge() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("pos", "Seq<u64>");

    ctx.push_assume("pos_len", "pos.len() == 4");
    // Bad order: [0, 3, 2, 1] → pos = [0, 3, 2, 1]
    ctx.push_assume("pos0", "pos.index(0) == 0");
    ctx.push_assume("pos1", "pos.index(1) == 3");
    ctx.push_assume("pos2", "pos.index(2) == 2");
    ctx.push_assume("pos3", "pos.index(3) == 1");

    // Edge 1→3 requires pos[1] < pos[3], but pos[1]=3 > pos[3]=1
    ctx.push_assert("edge_13_order", "pos.index(1) < pos.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 35g SOUNDNESS: wrong topological order should be rejected, got: {:?}",
        result,
    );
}

/// Tier 35h: Claiming no cycle when all in-degrees are positive is wrong.
#[test]
fn test_vt_tier35h_false_no_cycle_claim_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("indeg", "Seq<u64>");
    ctx.declare_var_parsed("out_len", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_val", "n == 3");
    ctx.push_assume("indeg_len", "indeg.len() == 3");
    ctx.push_assume("d0", "indeg.index(0) == 1");
    ctx.push_assume("d1", "indeg.index(1) == 1");
    ctx.push_assume("d2", "indeg.index(2) == 1");
    ctx.push_assume("empty_output", "out_len == 0");

    // WRONG: claiming output is complete despite cycle
    ctx.push_assert("false_complete", "out_len == n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 35h SOUNDNESS: false no-cycle claim should be rejected, got: {:?}",
        result,
    );
}
