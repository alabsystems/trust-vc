// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 58 — Bellman-Ford Shortest Paths VCs.
//!
//! Part 2: Symbolic relaxation properties and soundness negatives.
//! Split from `test_verifythis_bellman_ford.rs` to stay under the
//! 500-line guidance.
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

// ========================================================================
// GROUP E: Symbolic relaxation properties
// ========================================================================

/// Tier 58e: Symbolic — Bellman-Ford relaxation monotonically improves
/// or stays the same. For any edge (u,v,w): dist'[v] <= dist[v].
#[test]
fn test_vt_tier58e_symbolic_relaxation_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64");
    ctx.declare_var_parsed("dist_v", "i64");
    ctx.declare_var_parsed("w", "i64");
    ctx.declare_var_parsed("dist_v_new", "i64");

    ctx.push_assume("dist_u_bounded", "dist_u > -1000000 && dist_u < 1000000");
    ctx.push_assume("w_bounded", "w > -1000 && w < 1000");
    // Relaxation: dist'[v] = min(dist[v], dist[u] + w)
    // If dist[u] + w < dist[v], update; otherwise keep
    ctx.push_assume(
        "relax_rule",
        "dist_v_new == if dist_u + w < dist_v { dist_u + w } else { dist_v }",
    );

    // New distance never exceeds old distance
    ctx.push_assert("monotone", "dist_v_new <= dist_v");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58e: symbolic relaxation monotonicity should verify, got: {:?}",
        result,
    );
}

/// Tier 58e: Symbolic — if no edge can relax, optimality holds.
/// For all edges (u,v,w): dist[v] <= dist[u] + w ⟹ dist is optimal.
#[test]
fn test_vt_tier58e_symbolic_no_relax_implies_optimal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64");
    ctx.declare_var_parsed("dist_v", "i64");
    ctx.declare_var_parsed("w", "i64");

    // No relaxation possible
    ctx.push_assume("no_relax", "dist_v <= dist_u + w");
    // If we tried to relax, result equals dist_v (no change)
    ctx.declare_var_parsed("dist_v_new", "i64");
    ctx.push_assume(
        "try_relax",
        "dist_v_new == if dist_u + w < dist_v { dist_u + w } else { dist_v }",
    );
    ctx.push_assert("optimal", "dist_v_new == dist_v");
    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 58e: no-relaxation optimality should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 58f NEGATIVE: Claiming Dijkstra's distances work with negative edges.
/// Graph: 0→1(2), 0→2(5), 1→2(-4). Dijkstra visits 0, then 1 (dist=2),
/// then 2 (dist=5). But true shortest 0→2 = 0→1→2 = 2+(-4) = -2.
/// Dijkstra gives dist[2]=5, true is -2.
#[test]
fn test_vt_tier58f_dijkstra_wrong_with_neg_weights() {
    let mut ctx = VerificationContext::new();
    // Dijkstra's answer (wrong for negative edges)
    assume_seq_i64(&mut ctx, "dijkstra_dist", &[0, 2, 5]);

    // True shortest via negative edge: 0→1→2 = 2+(-4) = -2
    ctx.declare_var_parsed("true_dist_2", "i64");
    ctx.push_assume("true_calc", "true_dist_2 == 2 + -4");

    // Claiming Dijkstra's dist[2] is optimal should FAIL
    ctx.push_assert("dijkstra_optimal", "dijkstra_dist.index(2) <= true_dist_2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 58f SOUNDNESS: Dijkstra should fail with negative edges, got: {:?}",
        result,
    );
}

/// Tier 58f NEGATIVE: Claiming no negative cycle when one exists.
/// Graph: 0→1(1), 1→2(-3), 2→0(1). Cycle weight = -1.
/// After n-1=2 iterations, dist=[0, 1, -2].
/// Claiming dist satisfies optimality (no edge can relax) should FAIL
/// because edge 2→0 can still relax: dist[2]+1=-1 < dist[0]=0.
#[test]
fn test_vt_tier58f_missed_negative_cycle() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 1, -2]);

    // Edge 2→0 weight 1
    // Claiming optimality on this edge: dist[0] <= dist[2] + 1
    // dist[0]=0, dist[2]+1=-2+1=-1, 0 <= -1 is FALSE
    ctx.push_assert("false_optimal_20", "dist.index(0) <= dist.index(2) + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 58f SOUNDNESS: missed negative cycle should be detected, got: {:?}",
        result,
    );
}

/// Tier 58f NEGATIVE: A malformed edge list must invalidate the claimed
/// negative-edge relaxation. Retargeting the `1 -> 3` edge to node 2 makes the
/// old shortest-path equation false.
#[test]
fn test_vt_tier58f_edge_list_layout_mismatch_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 6, 7, 2]);
    assume_seq_u64(&mut ctx, "esrc", &[0, 0, 1, 1, 2]);
    assume_seq_u64(&mut ctx, "edst", &[1, 2, 2, 2, 3]);
    assume_seq_i64(&mut ctx, "ewt", &[6, 7, 8, -4, 9]);

    ctx.push_assert(
        "wrong_neg_edge_layout",
        "dist.index(edst.index(3)) == dist.index(esrc.index(3)) + ewt.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 58f SOUNDNESS: malformed edge list should break the negative-edge claim, got: {:?}",
        result,
    );
}

/// Tier 58f NEGATIVE: Off-by-one in relaxation — adding weight twice.
/// Edge 0→1 (weight 6), dist[0]=0. Wrong: dist'[1] = dist[0] + 2*w = 12.
/// True: dist'[1] = 0 + 6 = 6. Claiming 12 == 6 should fail.
#[test]
fn test_vt_tier58f_double_weight_relaxation_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_src", "i64");
    ctx.declare_var_parsed("w", "i64");
    ctx.declare_var_parsed("dist_wrong", "i64");

    ctx.push_assume("src_val", "dist_src == 0");
    ctx.push_assume("w_val", "w == 6");
    ctx.push_assume("wrong_relax", "dist_wrong == dist_src + w + w");

    // Claiming wrong result equals correct
    ctx.push_assert("wrong_eq_correct", "dist_wrong == dist_src + w");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 58f SOUNDNESS: double-weight relaxation should be rejected, got: {:?}",
        result,
    );
}
