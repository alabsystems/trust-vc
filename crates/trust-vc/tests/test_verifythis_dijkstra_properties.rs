// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 57 — Dijkstra's Shortest Path VCs.
//!
//! Part 2: Symbolic relaxation properties and soundness negatives.
//! Split from `test_verifythis_dijkstra.rs` to stay under the
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

const INF: i64 = 1000000;

// ========================================================================
// GROUP E: Symbolic relaxation property
// ========================================================================

/// Tier 57e: Symbolic — relaxation maintains triangle inequality.
/// For any edge (u,v) with weight w >= 0: if dist[v] > dist[u] + w,
/// then dist'[v] = dist[u] + w satisfies dist'[v] >= 0.
#[test]
fn test_vt_tier57e_symbolic_relaxation_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64");
    ctx.declare_var_parsed("dist_v", "i64");
    ctx.declare_var_parsed("w", "i64");
    ctx.declare_var_parsed("dist_v_new", "i64");

    ctx.push_assume("dist_u_nonneg", "dist_u >= 0");
    ctx.push_assume("w_nonneg", "w >= 0");
    ctx.push_assume("w_bounded", "w < 1000000");
    ctx.push_assume("dist_u_bounded", "dist_u < 1000000");
    // Relaxation condition and update
    ctx.push_assume("needs_relax", "dist_v > dist_u + w");
    ctx.push_assume("relax_update", "dist_v_new == dist_u + w");

    // New distance is non-negative
    ctx.push_assert("new_nonneg", "dist_v_new >= 0");
    // New distance satisfies triangle for this edge
    ctx.push_assert("triangle", "dist_v_new <= dist_u + w");
    // New distance is strictly better
    ctx.push_assert("improved", "dist_v_new < dist_v");
    // New distance is bounded
    ctx.push_assert("bounded", "dist_v_new < 2000000");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 57e: symbolic relaxation non-negativity should verify, got: {:?}",
        result,
    );
}

/// Tier 57e: Symbolic — no-op relaxation: if dist[v] <= dist[u] + w,
/// dist stays unchanged and triangle still holds.
#[test]
fn test_vt_tier57e_symbolic_noop_relaxation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64");
    ctx.declare_var_parsed("dist_v", "i64");
    ctx.declare_var_parsed("w", "i64");

    ctx.push_assume("dist_u_nonneg", "dist_u >= 0");
    ctx.push_assume("dist_v_nonneg", "dist_v >= 0");
    ctx.push_assume("w_nonneg", "w >= 0");
    // No relaxation needed
    ctx.push_assume("no_relax", "dist_v <= dist_u + w");

    ctx.push_assert("no_relax_feasible", "dist_v <= dist_u + w && dist_v >= 0");
    ctx.push_assert("rhs_nonneg", "dist_u + w >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 57e: no-op relaxation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 57f NEGATIVE: Wrong relaxation — using max instead of min.
/// If we set dist'[v] = max(dist[v], dist[u]+w) instead of min,
/// the triangle inequality fails.
#[test]
fn test_vt_tier57f_wrong_relaxation_max_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64");
    ctx.declare_var_parsed("dist_v", "i64");
    ctx.declare_var_parsed("w", "i64");
    ctx.declare_var_parsed("dist_v_new", "i64");

    ctx.push_assume("dist_u_nonneg", "dist_u >= 0");
    ctx.push_assume("dist_v_nonneg", "dist_v >= 0");
    ctx.push_assume("w_nonneg", "w >= 0");
    ctx.push_assume("dist_u_bounded", "dist_u < 1000");
    ctx.push_assume("dist_v_bounded", "dist_v < 1000");
    ctx.push_assume("w_bounded", "w < 1000");
    // WRONG: max instead of min
    ctx.push_assume(
        "wrong_relax",
        "dist_v_new == if dist_v >= dist_u + w { dist_v } else { dist_u + w }",
    );

    // Triangle inequality: dist'[v] <= dist[u] + w should FAIL
    ctx.push_assert("wrong_triangle", "dist_v_new <= dist_u + w");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 57f SOUNDNESS: max relaxation should reject triangle inequality, got: {:?}",
        result,
    );
}

/// Tier 57f NEGATIVE: Negative weight breaks Dijkstra's greedy property.
/// With edge 1→2 weight=-3 and dist=[0, 1, INF], after visiting node 1
/// we get dist[2] = 1 + (-3) = -2. But Dijkstra extracts node 0 first
/// (dist=0 > -2), so the greedy property "extracted dist is non-decreasing"
/// is violated.
#[test]
fn test_vt_tier57f_negative_weight_breaks_greedy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dist_u", "i64"); // dist of extracted node
    ctx.declare_var_parsed("dist_v_new", "i64"); // dist after relaxation

    ctx.push_assume("dist_u_val", "dist_u == 1");
    // Negative weight: w = -3
    ctx.push_assume("neg_relax", "dist_v_new == dist_u + -3");

    // Greedy property: extracted distances are non-decreasing.
    // dist_v_new should be >= 0 (since source dist was 0). But -2 < 0.
    ctx.push_assert("nonneg_dist", "dist_v_new >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 57f SOUNDNESS: negative weight should break non-negativity, got: {:?}",
        result,
    );
}

/// Tier 57f NEGATIVE: Claiming a non-shortest path is optimal.
/// Graph: 0→1(4), 0→2(2), 2→1(1). True shortest 0→1 is 3 (via 2).
/// Claiming dist[1]=4 (direct edge) is optimal should fail.
#[test]
fn test_vt_tier57f_non_optimal_path_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dist", &[0, 4, 2, INF]);
    assume_seq_i64(&mut ctx, "weights", &[4, 2, 1, 5]);

    // Claiming dist[1] satisfies triangle for edge 2→1 (should be 3, not 4)
    // Triangle: dist[1] <= dist[2] + w(2,1) = 2 + 1 = 3
    // But dist[1] = 4 > 3, so this fails
    ctx.push_assert(
        "wrong_triangle_21",
        "dist.index(1) <= dist.index(2) + weights.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 57f SOUNDNESS: non-optimal path should violate triangle inequality, got: {:?}",
        result,
    );
}

/// Tier 57f NEGATIVE: A malformed CSR layout must invalidate the claimed path.
/// Swapping node 2's outgoing targets turns the `2 -> 1` edge into `2 -> 3`,
/// so reusing the original shortest-path equality should fail.
#[test]
fn test_vt_tier57f_csr_layout_mismatch_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "row_starts", &[0, 2, 2, 4, 4]);
    assume_seq_u64(&mut ctx, "targets", &[1, 2, 3, 1]);
    assume_seq_i64(&mut ctx, "weights", &[4, 2, 1, 5]);
    assume_seq_i64(&mut ctx, "dist", &[0, 3, 2, 7]);

    ctx.push_assert(
        "wrong_csr_edge_claim",
        "dist.index(targets.index(row_starts.index(2))) \
         == dist.index(2) + weights.index(row_starts.index(2))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 57f SOUNDNESS: malformed CSR layout should break the claimed path, got: {:?}",
        result,
    );
}
