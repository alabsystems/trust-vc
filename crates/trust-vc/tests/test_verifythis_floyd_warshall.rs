// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 78 - Floyd-Warshall All-Pairs Shortest Paths VCs.
//!
//! Floyd-Warshall improves a distance matrix by allowing one more intermediate
//! vertex at each stage:
//!   dist_k[i][j] = min(dist_{k-1}[i][j], dist_{k-1}[i][k] + dist_{k-1}[k][j])
//!
//! Concrete 4-node directed graph (`INF = 100`):
//!   0 -> 1 (3), 0 -> 2 (9), 0 -> 3 (10)
//!   1 -> 2 (4), 1 -> 3 (8)
//!   2 -> 3 (2)
//!
//! Stage traces used below:
//!   dist0: direct edges only
//!     row0 = [0,   3,   9, 10]
//!     row1 = [100, 0,   4,  8]
//!     row2 = [100, 100, 0,  2]
//!     row3 = [100, 100, 100, 0]
//!   dist1: allow intermediate vertex 1
//!     row0 = [0, 3, 7, 10]    (0 -> 1 -> 2 shortens 0 -> 2)
//!   dist2: allow intermediate vertex 2
//!     row0 = [0, 3, 7, 9]     (0 -> 1 -> 2 -> 3 shortens 0 -> 3)
//!     row1 = [100, 0, 4, 6]   (1 -> 2 -> 3 shortens 1 -> 3)
//!
//! 12 tests: 8 positive (base matrix, relaxations, monotonicity, witness) + 4 negatives.
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

fn assume_floyd_warshall_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "dist0_row0", &[0, 3, 9, 10]);
    assume_seq_u64(ctx, "dist0_row1", &[100, 0, 4, 8]);
    assume_seq_u64(ctx, "dist0_row2", &[100, 100, 0, 2]);
    assume_seq_u64(ctx, "dist0_row3", &[100, 100, 100, 0]);

    assume_seq_u64(ctx, "dist1_row0", &[0, 3, 7, 10]);
    assume_seq_u64(ctx, "dist1_row1", &[100, 0, 4, 8]);
    assume_seq_u64(ctx, "dist1_row2", &[100, 100, 0, 2]);
    assume_seq_u64(ctx, "dist1_row3", &[100, 100, 100, 0]);

    assume_seq_u64(ctx, "dist2_row0", &[0, 3, 7, 9]);
    assume_seq_u64(ctx, "dist2_row1", &[100, 0, 4, 6]);
    assume_seq_u64(ctx, "dist2_row2", &[100, 100, 0, 2]);
    assume_seq_u64(ctx, "dist2_row3", &[100, 100, 100, 0]);
}

// ========================================================================
// GROUP A: Direct-edge matrix and sentinels
// ========================================================================

/// Tier 78a: the direct-edge matrix has zero diagonal and the expected base edges.
#[test]
fn test_vt_tier78a_direct_edge_matrix_has_zero_diagonal() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert("diag_0", "dist0_row0.index(0) == 0");
    ctx.push_assert("diag_1", "dist0_row1.index(1) == 0");
    ctx.push_assert("diag_2", "dist0_row2.index(2) == 0");
    ctx.push_assert("diag_3", "dist0_row3.index(3) == 0");
    ctx.push_assert("edge_01", "dist0_row0.index(1) == 3");
    ctx.push_assert("edge_12", "dist0_row1.index(2) == 4");
    ctx.push_assert("edge_23", "dist0_row2.index(3) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78a: direct-edge matrix should verify, got: {:?}",
        result,
    );
}

/// Tier 78a: absent edges stay at the finite INF sentinel in the base matrix.
#[test]
fn test_vt_tier78a_unreachable_edges_use_inf_sentinel() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert("row1_to_0_inf", "dist0_row1.index(0) == 100");
    ctx.push_assert("row2_to_0_inf", "dist0_row2.index(0) == 100");
    ctx.push_assert("row2_to_1_inf", "dist0_row2.index(1) == 100");
    ctx.push_assert("row3_to_2_inf", "dist0_row3.index(2) == 100");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78a: INF sentinels for absent edges should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Intermediate vertex 1 updates
// ========================================================================

/// Tier 78b: allowing vertex 1 shortens 0 -> 2 from 9 to 7.
#[test]
fn test_vt_tier78b_vertex_one_relaxes_zero_to_two() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "relax_0_2_via_1",
        "dist1_row0.index(2) == dist0_row0.index(1) + dist0_row1.index(2)",
    );
    ctx.push_assert("relax_0_2_value", "dist1_row0.index(2) == 7");
    ctx.push_assert(
        "strict_improvement",
        "dist1_row0.index(2) < dist0_row0.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78b: vertex 1 should relax 0 -> 2, got: {:?}",
        result,
    );
}

/// Tier 78b: the detour 0 -> 1 -> 3 is longer than the direct edge, so 0 -> 3 stays 10.
#[test]
fn test_vt_tier78b_longer_detour_does_not_replace_direct_edge() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "detour_is_longer",
        "dist0_row0.index(1) + dist0_row1.index(3) > dist0_row0.index(3)",
    );
    ctx.push_assert(
        "row0_col3_unchanged",
        "dist1_row0.index(3) == dist0_row0.index(3)",
    );
    ctx.push_assert("row0_col3_value", "dist1_row0.index(3) == 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78b: longer detour should not replace the direct edge, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Intermediate vertex 2 updates
// ========================================================================

/// Tier 78c: allowing vertex 2 shortens 1 -> 3 from 8 to 6.
#[test]
fn test_vt_tier78c_vertex_two_relaxes_one_to_three() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "relax_1_3_via_2",
        "dist2_row1.index(3) == dist1_row1.index(2) + dist1_row2.index(3)",
    );
    ctx.push_assert("relax_1_3_value", "dist2_row1.index(3) == 6");
    ctx.push_assert(
        "strict_improvement",
        "dist2_row1.index(3) < dist1_row1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78c: vertex 2 should relax 1 -> 3, got: {:?}",
        result,
    );
}

/// Tier 78c: allowing vertex 2 shortens 0 -> 3 from 10 to 9 using the staged 0 -> 2 distance.
#[test]
fn test_vt_tier78c_vertex_two_relaxes_zero_to_three() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "relax_0_3_via_2",
        "dist2_row0.index(3) == dist1_row0.index(2) + dist1_row2.index(3)",
    );
    ctx.push_assert("relax_0_3_value", "dist2_row0.index(3) == 9");
    ctx.push_assert(
        "strict_improvement",
        "dist2_row0.index(3) < dist1_row0.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78c: vertex 2 should relax 0 -> 3, got: {:?}",
        result,
    );
}

/// Tier 78c: later stages are pointwise monotone non-increasing on the affected rows.
#[test]
fn test_vt_tier78c_stage_distances_are_monotone() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "row0_col2_stable",
        "dist2_row0.index(2) == dist1_row0.index(2)",
    );
    ctx.push_assert(
        "row0_col3_monotone",
        "dist2_row0.index(3) <= dist1_row0.index(3)",
    );
    ctx.push_assert(
        "row1_col3_monotone",
        "dist2_row1.index(3) <= dist1_row1.index(3)",
    );
    ctx.push_assert(
        "row2_col3_stable",
        "dist2_row2.index(3) == dist1_row2.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78c: stage distances should be monotone, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Final witness path
// ========================================================================

/// Tier 78d: the witness path 0 -> 1 -> 2 -> 3 has weight 9 and matches the final distance.
#[test]
fn test_vt_tier78d_witness_path_matches_final_distance() {
    let mut ctx = VerificationContext::new();
    assume_floyd_warshall_example(&mut ctx);

    ctx.push_assert(
        "witness_sum",
        "dist2_row0.index(3) == dist0_row0.index(1) + dist0_row1.index(2) + dist0_row2.index(3)",
    );
    ctx.push_assert(
        "beats_direct_edge",
        "dist2_row0.index(3) < dist0_row0.index(3)",
    );
    ctx.push_assert(
        "final_1_3_beats_direct_edge",
        "dist2_row1.index(3) < dist0_row1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 78d: witness path should match the final distance, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Negative soundness checks
// ========================================================================

/// Tier 78e NEGATIVE: claiming 0 -> 2 shortens to 6 is too strong.
#[test]
fn test_vt_tier78e_too_short_zero_to_two_distance_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "dist1_row0", &[0, 3, 7, 10]);

    ctx.push_assert("wrong_0_2_value", "dist1_row0.index(2) == 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 78e SOUNDNESS: over-shortening 0 -> 2 should be rejected, got: {:?}",
        result,
    );
}

/// Tier 78e NEGATIVE: accepting the longer 0 -> 1 -> 3 detour as the stage-1 result is unsound.
#[test]
fn test_vt_tier78e_accepting_longer_detour_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "dist0_row0", &[0, 3, 9, 10]);
    assume_seq_u64(&mut ctx, "dist0_row1", &[100, 0, 4, 8]);
    assume_seq_u64(&mut ctx, "dist1_row0", &[0, 3, 7, 10]);

    ctx.push_assert(
        "wrong_stage1_detour",
        "dist1_row0.index(3) == dist0_row0.index(1) + dist0_row1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 78e SOUNDNESS: taking a longer detour should be rejected, got: {:?}",
        result,
    );
}

/// Tier 78e NEGATIVE: missing the 1 -> 3 improvement at stage 2 is unsound.
#[test]
fn test_vt_tier78e_missing_one_to_three_improvement_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "dist1_row1", &[100, 0, 4, 8]);
    assume_seq_u64(&mut ctx, "dist2_row1", &[100, 0, 4, 6]);

    ctx.push_assert(
        "wrong_stage2_13",
        "dist2_row1.index(3) == dist1_row1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 78e SOUNDNESS: missing the 1 -> 3 improvement should be rejected, got: {:?}",
        result,
    );
}

/// Tier 78e NEGATIVE: inventing a reverse path 2 -> 0 without any supporting edges is unsound.
#[test]
fn test_vt_tier78e_invented_reverse_path_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "dist2_row2", &[100, 100, 0, 2]);

    ctx.push_assert("invented_2_to_0", "dist2_row2.index(0) == 7");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 78e SOUNDNESS: invented reverse path should be rejected, got: {:?}",
        result,
    );
}
