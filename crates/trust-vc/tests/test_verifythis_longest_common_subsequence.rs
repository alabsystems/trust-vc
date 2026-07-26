// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 77 - Longest Common Subsequence (LCS) VCs.
//!
//! Given `a = [2, 5, 3, 7]` and `b = [5, 3, 2, 7]`, the DP recurrence is:
//!   dp[i][j] = dp[i-1][j-1] + 1,            if a[i-1] == b[j-1]
//!   dp[i][j] = max(dp[i-1][j], dp[i][j-1]), otherwise
//!
//! DP table:
//!         ""  5  3  2  7        Match transitions:
//!   ""  [  0  0  0  0  0 ]        dp[1][3] = dp[0][2]+1 = 1  (a[0]=2==b[2]=2)
//!    2  [  0  0  0  1  1 ]        dp[2][1] = dp[1][0]+1 = 1  (a[1]=5==b[0]=5)
//!    5  [  0  1  1  1  1 ]        dp[3][2] = dp[2][1]+1 = 2  (a[2]=3==b[1]=3)
//!    3  [  0  1  2  2  2 ]        dp[4][4] = dp[3][3]+1 = 3  (a[3]=7==b[3]=7)
//!    7  [  0  1  2  2  3 ]
//!
//! LCS length = 3.  Witness: [5, 3, 7] at a-indices [1,2,3], b-indices [0,1,3].
//!
//! 17 tests: 13 positive (base cases, match/mismatch transitions, witness) + 4 negatives.
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

fn assume_lcs_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "a", &[2, 5, 3, 7]);
    assume_seq_u64(ctx, "b", &[5, 3, 2, 7]);
    assume_seq_u64(ctx, "dp_row0", &[0, 0, 0, 0, 0]);
    assume_seq_u64(ctx, "dp_row1", &[0, 0, 0, 1, 1]);
    assume_seq_u64(ctx, "dp_row2", &[0, 1, 1, 1, 1]);
    assume_seq_u64(ctx, "dp_row3", &[0, 1, 2, 2, 2]);
    assume_seq_u64(ctx, "dp_row4", &[0, 1, 2, 2, 3]);
}

fn assume_lcs_witness(ctx: &mut VerificationContext) {
    // Witness LCS = [5, 3, 7] with a-indices [1,2,3] and b-indices [0,1,3].
    assume_seq_u64(ctx, "lcs", &[5, 3, 7]);
    assume_seq_u64(ctx, "lcs_a_idx", &[1, 2, 3]);
    assume_seq_u64(ctx, "lcs_b_idx", &[0, 1, 3]);
}

// ========================================================================
// GROUP A: Base cases and DP table structure
// ========================================================================

/// Tier 77a: the base row (empty a-prefix) is all zeros.
#[test]
fn test_vt_tier77a_base_row_all_zeros() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("base_row_0", "dp_row0.index(0) == 0");
    ctx.push_assert("base_row_1", "dp_row0.index(1) == 0");
    ctx.push_assert("base_row_2", "dp_row0.index(2) == 0");
    ctx.push_assert("base_row_3", "dp_row0.index(3) == 0");
    ctx.push_assert("base_row_4", "dp_row0.index(4) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77a: base row should be all zeros, got: {:?}",
        result,
    );
}

/// Tier 77a: the base column (empty b-prefix) is all zeros.
#[test]
fn test_vt_tier77a_base_column_all_zeros() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("base_col_0", "dp_row0.index(0) == 0");
    ctx.push_assert("base_col_1", "dp_row1.index(0) == 0");
    ctx.push_assert("base_col_2", "dp_row2.index(0) == 0");
    ctx.push_assert("base_col_3", "dp_row3.index(0) == 0");
    ctx.push_assert("base_col_4", "dp_row4.index(0) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77a: base column should be all zeros, got: {:?}",
        result,
    );
}

/// Tier 77a: DP values are non-decreasing along each row (left to right).
#[test]
fn test_vt_tier77a_rows_non_decreasing() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    // Row 4 (final row) should be non-decreasing: 0 <= 1 <= 2 <= 2 <= 3.
    ctx.push_assert("r4_mono_01", "dp_row4.index(1) >= dp_row4.index(0)");
    ctx.push_assert("r4_mono_12", "dp_row4.index(2) >= dp_row4.index(1)");
    ctx.push_assert("r4_mono_23", "dp_row4.index(3) >= dp_row4.index(2)");
    ctx.push_assert("r4_mono_34", "dp_row4.index(4) >= dp_row4.index(3)");
    // Row 3 likewise.
    ctx.push_assert("r3_mono_01", "dp_row3.index(1) >= dp_row3.index(0)");
    ctx.push_assert("r3_mono_12", "dp_row3.index(2) >= dp_row3.index(1)");
    ctx.push_assert("r3_mono_23", "dp_row3.index(3) >= dp_row3.index(2)");
    ctx.push_assert("r3_mono_34", "dp_row3.index(4) >= dp_row3.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77a: DP rows should be non-decreasing, got: {:?}",
        result,
    );
}

/// Tier 77a: DP values are non-decreasing along each column (top to bottom).
#[test]
fn test_vt_tier77a_columns_non_decreasing() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    // Column 4 (rightmost): 0 <= 1 <= 1 <= 2 <= 3.
    ctx.push_assert("c4_mono_01", "dp_row1.index(4) >= dp_row0.index(4)");
    ctx.push_assert("c4_mono_12", "dp_row2.index(4) >= dp_row1.index(4)");
    ctx.push_assert("c4_mono_23", "dp_row3.index(4) >= dp_row2.index(4)");
    ctx.push_assert("c4_mono_34", "dp_row4.index(4) >= dp_row3.index(4)");
    // Column 2: 0 <= 0 <= 1 <= 2 <= 2.
    ctx.push_assert("c2_mono_01", "dp_row1.index(2) >= dp_row0.index(2)");
    ctx.push_assert("c2_mono_12", "dp_row2.index(2) >= dp_row1.index(2)");
    ctx.push_assert("c2_mono_23", "dp_row3.index(2) >= dp_row2.index(2)");
    ctx.push_assert("c2_mono_34", "dp_row4.index(2) >= dp_row3.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77a: DP columns should be non-decreasing, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Match transitions (a[i-1] == b[j-1] → dp[i-1][j-1] + 1)
// ========================================================================

/// Tier 77b: dp[1][3] = 1 because a[0]=2 == b[2]=2, so dp[0][2] + 1 = 1.
#[test]
fn test_vt_tier77b_match_a0_b2_increments_diagonal() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_match", "a.index(0) == b.index(2)");
    ctx.push_assert(
        "dp_13_from_diagonal",
        "dp_row1.index(3) == dp_row0.index(2) + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77b: match transition dp[1][3] should verify, got: {:?}",
        result,
    );
}

/// Tier 77b: dp[2][1] = 1 because a[1]=5 == b[0]=5, so dp[1][0] + 1 = 1.
#[test]
fn test_vt_tier77b_match_a1_b0_increments_diagonal() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_match", "a.index(1) == b.index(0)");
    ctx.push_assert(
        "dp_21_from_diagonal",
        "dp_row2.index(1) == dp_row1.index(0) + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77b: match transition dp[2][1] should verify, got: {:?}",
        result,
    );
}

/// Tier 77b: dp[3][2] = 2 because a[2]=3 == b[1]=3, so dp[2][1] + 1 = 2.
#[test]
fn test_vt_tier77b_match_a2_b1_builds_on_prior_lcs() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_match", "a.index(2) == b.index(1)");
    ctx.push_assert(
        "dp_32_from_diagonal",
        "dp_row3.index(2) == dp_row2.index(1) + 1",
    );
    ctx.push_assert("dp_32_value", "dp_row3.index(2) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77b: match transition dp[3][2] should verify, got: {:?}",
        result,
    );
}

/// Tier 77b: dp[4][4] = 3 because a[3]=7 == b[3]=7, so dp[3][3] + 1 = 3.
#[test]
fn test_vt_tier77b_final_match_yields_lcs_length_three() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_match", "a.index(3) == b.index(3)");
    ctx.push_assert(
        "dp_44_from_diagonal",
        "dp_row4.index(4) == dp_row3.index(3) + 1",
    );
    ctx.push_assert("lcs_length_is_three", "dp_row4.index(4) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77b: final match dp[4][4] = 3 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Mismatch transitions and witness verification
// ========================================================================

/// Tier 77c: dp[1][1] = max(dp[0][1], dp[1][0]) = 0 because a[0]=2 != b[0]=5.
#[test]
fn test_vt_tier77c_mismatch_a0_b0_takes_max_of_neighbors() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_differ", "!(a.index(0) == b.index(0))");
    ctx.push_assert("dp_11_geq_left", "dp_row1.index(1) >= dp_row1.index(0)");
    ctx.push_assert("dp_11_geq_top", "dp_row1.index(1) >= dp_row0.index(1)");
    ctx.push_assert("dp_11_value", "dp_row1.index(1) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77c: mismatch dp[1][1] should take max of neighbors, got: {:?}",
        result,
    );
}

/// Tier 77c: dp[3][3] = max(dp[2][3], dp[3][2]) = 2 because a[2]=3 != b[2]=2.
#[test]
fn test_vt_tier77c_mismatch_a2_b2_propagates_best_subproblem() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_differ", "!(a.index(2) == b.index(2))");
    ctx.push_assert("dp_33_geq_left", "dp_row3.index(3) >= dp_row3.index(2)");
    ctx.push_assert("dp_33_geq_top", "dp_row3.index(3) >= dp_row2.index(3)");
    ctx.push_assert("dp_33_value", "dp_row3.index(3) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77c: mismatch dp[3][3] should propagate best, got: {:?}",
        result,
    );
}

/// Tier 77c: dp[4][3] = max(dp[3][3], dp[4][2]) = 2 because a[3]=7 != b[2]=2.
#[test]
fn test_vt_tier77c_mismatch_a3_b2_holds_prior_best() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("values_differ", "!(a.index(3) == b.index(2))");
    ctx.push_assert("dp_43_geq_left", "dp_row4.index(3) >= dp_row4.index(2)");
    ctx.push_assert("dp_43_geq_top", "dp_row4.index(3) >= dp_row3.index(3)");
    ctx.push_assert("dp_43_value", "dp_row4.index(3) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77c: mismatch dp[4][3] should hold prior best, got: {:?}",
        result,
    );
}

/// Tier 77c: the witness [5, 3, 7] has matching values at the claimed indices.
#[test]
fn test_vt_tier77c_witness_values_match_at_claimed_indices() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);
    assume_lcs_witness(&mut ctx);

    // lcs[k] == a[lcs_a_idx[k]] == b[lcs_b_idx[k]] for each k.
    ctx.push_assert(
        "witness_0_in_a",
        "lcs.index(0) == a.index(lcs_a_idx.index(0))",
    );
    ctx.push_assert(
        "witness_0_in_b",
        "lcs.index(0) == b.index(lcs_b_idx.index(0))",
    );
    ctx.push_assert(
        "witness_1_in_a",
        "lcs.index(1) == a.index(lcs_a_idx.index(1))",
    );
    ctx.push_assert(
        "witness_1_in_b",
        "lcs.index(1) == b.index(lcs_b_idx.index(1))",
    );
    ctx.push_assert(
        "witness_2_in_a",
        "lcs.index(2) == a.index(lcs_a_idx.index(2))",
    );
    ctx.push_assert(
        "witness_2_in_b",
        "lcs.index(2) == b.index(lcs_b_idx.index(2))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77c: witness values should match at claimed indices, got: {:?}",
        result,
    );
}

/// Tier 77c: the witness indices are strictly increasing in both sequences.
#[test]
fn test_vt_tier77c_witness_indices_strictly_increasing() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);
    assume_lcs_witness(&mut ctx);

    // a-indices: 1 < 2 < 3.
    ctx.push_assert("a_idx_01", "lcs_a_idx.index(0) + 1 <= lcs_a_idx.index(1)");
    ctx.push_assert("a_idx_12", "lcs_a_idx.index(1) + 1 <= lcs_a_idx.index(2)");
    // b-indices: 0 < 1 < 3.
    ctx.push_assert("b_idx_01", "lcs_b_idx.index(0) + 1 <= lcs_b_idx.index(1)");
    ctx.push_assert("b_idx_12", "lcs_b_idx.index(1) + 1 <= lcs_b_idx.index(2)");
    // Witness length matches LCS length.
    ctx.push_assert("witness_len", "lcs.len() == dp_row4.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 77c: witness indices should be strictly increasing, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 77d NEGATIVE: claiming LCS length is 4 when the DP answer is 3.
#[test]
fn test_vt_tier77d_overclaiming_lcs_length_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("lcs_length_four", "dp_row4.index(4) == 4");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 77d SOUNDNESS: claiming LCS = 4 should be rejected, got: {:?}",
        result,
    );
}

/// Tier 77d NEGATIVE: using the match transition when values differ is unsound.
#[test]
fn test_vt_tier77d_match_transition_on_mismatch_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    // a[0]=2, b[0]=5: these differ, so dp[1][1] should NOT equal dp[0][0]+1 = 1.
    ctx.push_assert(
        "wrong_match_transition",
        "dp_row1.index(1) == dp_row0.index(0) + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 77d SOUNDNESS: match transition on mismatch should be rejected, got: {:?}",
        result,
    );
}

/// Tier 77d NEGATIVE: claiming dp[3][2] = 3 violates the DP recurrence.
#[test]
fn test_vt_tier77d_inflated_dp_value_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    ctx.push_assert("inflated_dp_32", "dp_row3.index(2) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 77d SOUNDNESS: inflated dp value should be rejected, got: {:?}",
        result,
    );
}

/// Tier 77d NEGATIVE: column-decreasing dp[4][2] < dp[3][2] violates monotonicity.
#[test]
fn test_vt_tier77d_column_decrease_violates_monotonicity() {
    let mut ctx = VerificationContext::new();
    assume_lcs_example(&mut ctx);

    // dp_row4.index(2) = 2 and dp_row3.index(2) = 2, so strict decrease is false.
    ctx.push_assert(
        "column_decrease",
        "dp_row4.index(2) + 1 <= dp_row3.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 77d SOUNDNESS: column-decreasing dp should be rejected, got: {:?}",
        result,
    );
}
