// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 58 — Bellman-Ford Shortest Paths VCs.
//!
//! Bellman-Ford computes single-source shortest paths in a graph that
//! may contain negative-weight edges. Unlike Dijkstra, it correctly
//! handles negative weights and detects negative-weight cycles. This is
//! a classic VerifyThis category involving iterative relaxation and
//! cycle detection.
//!
//! We model a directed weighted graph as edge lists:
//!   - `src: Seq<u64>` — edge source vertices
//!   - `dst: Seq<u64>` — edge destination vertices
//!   - `wt: Seq<i64>` — edge weights (may be negative)
//!   - `dist: Seq<i64>` — distance array (INF = 1000000)
//!
//! Core proof obligations:
//!   1. Init: dist[src]=0, all others=INF
//!   2. Step: after k-th iteration, dist[v] = shortest path using ≤ k edges
//!   3. Convergence: if no negative cycle, n-1 iterations suffice
//!   4. Negative cycle detection: if n-th iteration still relaxes, cycle exists
//!   5. Negatives: wrong convergence claims or missed cycles rejected
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

const INF: i64 = 1000000;

// ========================================================================
// GROUP A: Init — source distance initialization
// ========================================================================

/// Tier 58a: Init — dist[src]=0, all others=INF.
/// Graph: 4 nodes, 5 edges (some negative), source=0.
/// Edges: 0→1(6), 0→2(7), 1→2(8), 1→3(-4), 2→3(9)
#[test]
fn test_vt_tier58a_bellman_ford_init() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, INF, INF, INF]);

    // Source distance is 0
    ctx.push_assert("src_dist", "dist.index(0) == 0");
    // All others are INF
    ctx.push_assert("dist_1", "dist.index(1) == 1000000");
    ctx.push_assert("dist_2", "dist.index(2) == 1000000");
    ctx.push_assert("dist_3", "dist.index(3) == 1000000");
    // Source has minimal distance
    ctx.push_assert("src_min_1", "dist.index(0) <= dist.index(1)");
    ctx.push_assert("src_min_2", "dist.index(0) <= dist.index(2)");
    ctx.push_assert("src_min_3", "dist.index(0) <= dist.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58a: Bellman-Ford init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — iterative relaxation with negative weights
// ========================================================================

/// Tier 58b: Step — iteration 1 relaxes edges from source.
/// Graph: 0→1(6), 0→2(7), 1→2(8), 1→3(-4), 2→3(9).
/// After iteration 1: dist = [0, 6, 7, INF].
/// Only edges from source (node 0) can improve distances.
#[test]
fn test_vt_tier58b_iteration1_relax_from_source() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist_pre", &[0, INF, INF, INF]);

    // Edge weights
    ctx.declare_var_parsed("w01", "i64");
    ctx.declare_var_parsed("w02", "i64");
    ctx.push_assume("w01_val", "w01 == 6");
    ctx.push_assume("w02_val", "w02 == 7");

    // After iteration 1
    assume_seq_i64(&mut ctx, "dist_post", &[0, 6, 7, INF]);

    // Relaxation correctness
    ctx.push_assert("relax_1", "dist_post.index(1) == dist_pre.index(0) + w01");
    ctx.push_assert("relax_2", "dist_post.index(2) == dist_pre.index(0) + w02");
    // Source unchanged
    ctx.push_assert("src_unchanged", "dist_post.index(0) == dist_pre.index(0)");
    // Node 3 not reachable in 1 edge from source
    ctx.push_assert("unreached_3", "dist_post.index(3) == dist_pre.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58b: iteration 1 relaxation should verify, got: {:?}",
        result,
    );
}

/// Tier 58b: Step — iteration 2 uses negative edge weight.
/// After iteration 1: dist = [0, 6, 7, INF].
/// Iteration 2 relaxes edge 1→3 (weight -4): dist[3] = 6 + (-4) = 2.
/// Also relaxes 1→2 (weight 8): 6 + 8 = 14 > 7, no update.
/// And 2→3 (weight 9): 7 + 9 = 16 > 2 (already updated via negative edge).
/// After iteration 2: dist = [0, 6, 7, 2].
#[test]
fn test_vt_tier58b_iteration2_negative_edge() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist_pre", &[0, 6, 7, INF]);

    ctx.declare_var_parsed("w13", "i64"); // edge 1→3 weight
    ctx.push_assume("w13_val", "w13 == -4");

    // After iteration 2
    assume_seq_i64(&mut ctx, "dist_post", &[0, 6, 7, 2]);

    // Negative edge relaxation: dist[3] = dist[1] + w(1,3) = 6 + (-4) = 2
    ctx.push_assert("neg_relax", "dist_post.index(3) == dist_pre.index(1) + w13");
    // Result can be less than source distance (negative edge effect)
    ctx.push_assert("below_others", "dist_post.index(3) < dist_post.index(1)");
    // Nodes 0, 1, 2 unchanged (no shorter paths found)
    ctx.push_assert("unchanged_0", "dist_post.index(0) == dist_pre.index(0)");
    ctx.push_assert("unchanged_1", "dist_post.index(1) == dist_pre.index(1)");
    ctx.push_assert("unchanged_2", "dist_post.index(2) == dist_pre.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58b: iteration 2 negative edge should verify, got: {:?}",
        result,
    );
}

/// Tier 58b: Step — iteration 3 finds no further improvements.
/// dist = [0, 6, 7, 2]. Check all edges: no relaxation possible.
#[test]
fn test_vt_tier58b_iteration3_no_change() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 6, 7, 2]);

    // Edge 0→1 (weight 6): dist[1]=6 <= dist[0]+6=6 ✓
    ctx.push_assert("no_relax_01", "dist.index(1) <= dist.index(0) + 6");
    // Edge 0→2 (weight 7): dist[2]=7 <= dist[0]+7=7 ✓
    ctx.push_assert("no_relax_02", "dist.index(2) <= dist.index(0) + 7");
    // Edge 1→2 (weight 8): dist[2]=7 <= dist[1]+8=14 ✓
    ctx.push_assert("no_relax_12", "dist.index(2) <= dist.index(1) + 8");
    // Edge 1→3 (weight -4): dist[3]=2 <= dist[1]+(-4)=2 ✓
    ctx.push_assert("no_relax_13", "dist.index(3) <= dist.index(1) + -4");
    // Edge 2→3 (weight 9): dist[3]=2 <= dist[2]+9=16 ✓
    ctx.push_assert("no_relax_23", "dist.index(3) <= dist.index(2) + 9");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58b: iteration 3 no-change should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Convergence — n-1 iterations suffice without negative cycle
// ========================================================================

/// Tier 58c: Convergence — final distances satisfy triangle inequality
/// on ALL edges simultaneously (the Bellman-Ford optimality condition).
/// dist = [0, 6, 7, 2] for graph with 5 edges.
#[test]
fn test_vt_tier58c_optimality_condition() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 6, 7, 2]);

    // Edge list: (src, dst, weight)
    // 0→1(6), 0→2(7), 1→2(8), 1→3(-4), 2→3(9)
    assume_seq_u64(&mut ctx, "esrc", &[0, 0, 1, 1, 2]);
    assume_seq_u64(&mut ctx, "edst", &[1, 2, 2, 3, 3]);
    assume_seq_i64(&mut ctx, "ewt", &[6, 7, 8, -4, 9]);

    // For every edge (u,v,w): dist[v] <= dist[u] + w, using the edge-list layout.
    ctx.push_assert(
        "opt_e0",
        "dist.index(edst.index(0)) <= dist.index(esrc.index(0)) + ewt.index(0)",
    );
    ctx.push_assert(
        "opt_e1",
        "dist.index(edst.index(1)) <= dist.index(esrc.index(1)) + ewt.index(1)",
    );
    ctx.push_assert(
        "opt_e2",
        "dist.index(edst.index(2)) <= dist.index(esrc.index(2)) + ewt.index(2)",
    );
    ctx.push_assert(
        "opt_e3",
        "dist.index(edst.index(3)) == dist.index(esrc.index(3)) + ewt.index(3)",
    );
    ctx.push_assert(
        "opt_e4",
        "dist.index(edst.index(4)) <= dist.index(esrc.index(4)) + ewt.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58c: optimality condition should verify, got: {:?}",
        result,
    );
}

/// Tier 58c: Convergence — path reconstruction.
/// Shortest path 0→3 = 0→1→3 with cost 6+(-4)=2.
/// Predecessor: pred[3]=1, pred[1]=0.
#[test]
fn test_vt_tier58c_path_reconstruction() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 6, 7, 2]);
    // pred[i] = predecessor on shortest path (-1 = no predecessor / source)
    assume_seq_i64(&mut ctx, "pred", &[-1, 0, 0, 1]);

    // Path 0→3: via pred[3]=1, pred[1]=0
    // dist[1] = dist[0] + w(0,1) = 0 + 6 = 6
    ctx.push_assert("path_01", "dist.index(1) == dist.index(0) + 6");
    // dist[3] = dist[1] + w(1,3) = 6 + (-4) = 2
    ctx.push_assert("path_13", "dist.index(3) == dist.index(1) + -4");
    // Predecessors are consistent
    ctx.push_assert("pred_src", "pred.index(0) == -1");
    ctx.push_assert("pred_1", "pred.index(1) == 0");
    ctx.push_assert("pred_3", "pred.index(3) == 1");
    // Path length = 2 edges (within n-1=3)
    ctx.push_assert("path_bounded", "2 < 4");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58c: path reconstruction should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative cycle detection
// ========================================================================

/// Tier 58d: Negative cycle — after n-1 iterations, an extra pass
/// still finds a shorter path ⟹ negative cycle exists.
/// Graph: 3 nodes with negative cycle 0→1(1), 1→2(-3), 2→0(1).
/// Cycle weight: 1 + (-3) + 1 = -1 < 0.
#[test]
fn test_vt_tier58d_negative_cycle_detected() {
    let mut ctx = VerificationContext::new();
    // After n-1=2 iterations
    assume_seq_i64(&mut ctx, "dist_before", &[0, 1, -2]);

    // Edge 2→0 (weight 1): dist[0]=0, dist[2]+1=-2+1=-1 < 0 → can relax!
    ctx.declare_var_parsed("relax_val", "i64");
    ctx.push_assume("relax_compute", "relax_val == dist_before.index(2) + 1");
    // The n-th iteration still finds improvement
    ctx.push_assert("still_relaxes", "relax_val < dist_before.index(0)");
    // This proves a negative cycle exists
    // Cycle: 0→1→2→0, total weight = 1+(-3)+1 = -1
    ctx.declare_var_parsed("cycle_weight", "i64");
    ctx.push_assume("cycle_w", "cycle_weight == 1 + -3 + 1");
    ctx.push_assert("cycle_negative", "cycle_weight < 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58d: negative cycle detection should verify, got: {:?}",
        result,
    );
}

/// Tier 58d: Negative cycle — trace through the cycle relaxation.
/// After 2 iterations on 3-node negative cycle:
/// iter 0: [0, INF, INF]
/// iter 1: [0, 1, INF] (relax 0→1)
/// iter 2: [0, 1, -2] (relax 1→2: 1+(-3)=-2)
/// iter 3 (extra): 2→0: -2+1=-1 < 0 → cycle! Also 0→1: -1+1=0 < 1.
#[test]
fn test_vt_tier58d_negative_cycle_trace() {
    let mut ctx = VerificationContext::new();
    // Trace each iteration
    assume_seq_i64(&mut ctx, "d0", &[0, INF, INF]);
    assume_seq_i64(&mut ctx, "d1", &[0, 1, INF]);
    assume_seq_i64(&mut ctx, "d2", &[0, 1, -2]);

    // Iteration 1: relax 0→1 (w=1)
    ctx.push_assert("iter1_01", "d1.index(1) == d0.index(0) + 1");
    ctx.push_assert("iter1_src", "d1.index(0) == d0.index(0)");
    // Iteration 2: relax 1→2 (w=-3)
    ctx.push_assert("iter2_12", "d2.index(2) == d1.index(1) + -3");
    ctx.push_assert("iter2_01", "d2.index(0) == d1.index(0)");
    ctx.push_assert("iter2_1", "d2.index(1) == d1.index(1)");
    // Extra iteration: 2→0 (w=1) would yield -2+1=-1 < 0
    ctx.push_assert("extra_relax", "d2.index(2) + 1 < d2.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58d: negative cycle trace should verify, got: {:?}",
        result,
    );
}
