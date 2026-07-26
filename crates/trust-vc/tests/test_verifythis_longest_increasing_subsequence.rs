// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 75 - Longest Increasing Subsequence (LIS) VCs.
//!
//! The longest increasing subsequence is a fundamental dynamic programming
//! problem: given a sequence `a`, compute `dp[i]` = the length of the longest
//! strictly increasing subsequence ending at index `i`.  The transition is
//! `dp[i] = 1 + max { dp[j] : j < i, a[j] < a[i] }` (or 1 if no such j
//! exists).  The overall LIS length is `max { dp[i] }`.
//!
//! Core proof obligations:
//!   1. Every dp value is at least 1 (each element alone is a subsequence).
//!   2. The DP transition: if `a[j] < a[i]` and `j < i` then `dp[i] >= dp[j] + 1`.
//!   3. The DP value equals the actual best: dp[i] is tight (equals one
//!      of the `dp[j] + 1` values or 1 if no predecessor qualifies).
//!   4. The global LIS length is the maximum over all dp values.
//!   5. A witness subsequence of the claimed length exists.
//!   6. Negatives: claiming a dp value of 0, claiming the LIS exceeds
//!      the maximum dp value, or violating strict increase are unsound.
//!
//! Example sequence:
//!   a  = [2, 5, 3, 7, 1, 6, 8, 4]
//!   dp = [1, 2, 2, 3, 1, 3, 4, 3]
//!
//! Transition trace:
//!   dp[0] = 1          (no predecessor)
//!   dp[1] = 2          (a[0]=2 < a[1]=5, dp[0]+1 = 2)
//!   dp[2] = 2          (a[0]=2 < a[2]=3, dp[0]+1 = 2; a[1]=5 >= 3 skip)
//!   dp[3] = 3          (a[1]=5 < a[3]=7, dp[1]+1=3; a[2]=3 < 7, dp[2]+1=3)
//!   dp[4] = 1          (no a[j] < 1 for j < 4)
//!   dp[5] = 3          (a[1]=5 < a[5]=6, dp[1]+1=3)
//!   dp[6] = 4          (a[3]=7 < a[6]=8, dp[3]+1=4; a[5]=6 < 8, dp[5]+1=4)
//!   dp[7] = 3          (a[2]=3 < a[7]=4, dp[2]+1=3)
//!
//! LIS length = 4.  Witness: [2, 3, 7, 8] (indices 0, 2, 3, 6).
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

fn assume_lis_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "a", &[2, 5, 3, 7, 1, 6, 8, 4]);
    assume_seq_u64(ctx, "dp", &[1, 2, 2, 3, 1, 3, 4, 3]);
    // Witness subsequence: indices [0, 2, 3, 6] → values [2, 3, 7, 8]
    assume_seq_u64(ctx, "witness_idx", &[0, 2, 3, 6]);
    assume_seq_u64(ctx, "witness_val", &[2, 3, 7, 8]);
}

// ========================================================================
// GROUP A: Base cases — every dp value is at least 1
// ========================================================================

/// Tier 75a: the first element always has dp = 1 (no predecessor).
#[test]
fn test_vt_tier75a_first_element_dp_is_one() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("dp_0_is_one", "dp.index(0) == 1");
    ctx.push_assert("a_len_matches_dp_len", "a.len() == dp.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75a: first element dp should be 1, got: {:?}",
        result,
    );
}

/// Tier 75a: every dp value is at least 1.
#[test]
fn test_vt_tier75a_all_dp_values_at_least_one() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    for i in 0..8 {
        ctx.push_assert(&format!("dp_{i}_geq_one"), &format!("dp.index({i}) >= 1"));
    }

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75a: all dp values should be >= 1, got: {:?}",
        result,
    );
}

/// Tier 75a: elements with no smaller predecessor get dp = 1.
#[test]
fn test_vt_tier75a_no_predecessor_gives_dp_one() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    // Index 4: a[4] = 1, no a[j] < 1 for j < 4
    ctx.push_assert("dp_4_base_case", "dp.index(4) == 1");
    // Also: a[0]=2, a[1]=5, a[2]=3, a[3]=7 — none are < 1
    ctx.push_assert("no_pred_0", "!(a.index(0) < a.index(4))");
    ctx.push_assert("no_pred_1", "!(a.index(1) < a.index(4))");
    ctx.push_assert("no_pred_2", "!(a.index(2) < a.index(4))");
    ctx.push_assert("no_pred_3", "!(a.index(3) < a.index(4))");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75a: element with no smaller predecessor should have dp = 1, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: DP transition correctness
// ========================================================================

/// Tier 75b: dp[1] = dp[0] + 1 via the transition a[0] < a[1].
#[test]
fn test_vt_tier75b_transition_index_1() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("a0_lt_a1", "a.index(0) < a.index(1)");
    ctx.push_assert("dp1_geq_dp0_plus_1", "dp.index(1) >= dp.index(0) + 1");
    ctx.push_assert("dp1_exact", "dp.index(1) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75b: dp[1] should follow from dp[0]+1 transition, got: {:?}",
        result,
    );
}

/// Tier 75b: dp[3] = 3 via the best predecessor a[1]=5 < a[3]=7 giving dp[1]+1=3.
#[test]
fn test_vt_tier75b_transition_index_3_best_predecessor() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    // Two valid predecessors: j=1 (dp[1]+1=3) and j=2 (dp[2]+1=3), both give 3
    ctx.push_assert("a1_lt_a3", "a.index(1) < a.index(3)");
    ctx.push_assert("dp3_geq_dp1_plus_1", "dp.index(3) >= dp.index(1) + 1");
    ctx.push_assert("a2_lt_a3", "a.index(2) < a.index(3)");
    ctx.push_assert("dp3_geq_dp2_plus_1", "dp.index(3) >= dp.index(2) + 1");
    ctx.push_assert("dp3_exact", "dp.index(3) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75b: dp[3] should equal 3 via best predecessor, got: {:?}",
        result,
    );
}

/// Tier 75b: dp[6] = 4, the global maximum, via a[3]=7 < a[6]=8.
#[test]
fn test_vt_tier75b_transition_index_6_global_max() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("a3_lt_a6", "a.index(3) < a.index(6)");
    ctx.push_assert("dp6_geq_dp3_plus_1", "dp.index(6) >= dp.index(3) + 1");
    ctx.push_assert("dp6_exact", "dp.index(6) == 4");
    ctx.push_assert(
        "dp6_is_global_max",
        "dp.index(6) >= dp.index(0) && dp.index(6) >= dp.index(1) && dp.index(6) >= dp.index(2) && dp.index(6) >= dp.index(3) && dp.index(6) >= dp.index(4) && dp.index(6) >= dp.index(5) && dp.index(6) >= dp.index(7)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75b: dp[6] should be the global max via transition from dp[3], got: {:?}",
        result,
    );
}

/// Tier 75b: dp[7] = 3 via a[2]=3 < a[7]=4 giving dp[2]+1=3.
#[test]
fn test_vt_tier75b_transition_index_7() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("a2_lt_a7", "a.index(2) < a.index(7)");
    ctx.push_assert("dp7_geq_dp2_plus_1", "dp.index(7) >= dp.index(2) + 1");
    ctx.push_assert("dp7_exact", "dp.index(7) == 3");
    // Also verify that a[1]=5 >= a[7]=4, so index 1 is not a valid predecessor
    ctx.push_assert("a1_geq_a7", "!(a.index(1) < a.index(7))");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75b: dp[7] should be 3 via transition from dp[2], got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: LIS length and witness correctness
// ========================================================================

/// Tier 75c: the LIS length equals the maximum dp value.
#[test]
fn test_vt_tier75c_lis_length_is_max_dp() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);
    ctx.declare_var_parsed("lis_len", "u64");
    ctx.push_assume("lis_len_val", "lis_len == 4");

    ctx.push_assert("lis_len_matches_dp6", "lis_len == dp.index(6)");
    // dp[6] dominates all others
    for i in 0..8 {
        ctx.push_assert(
            &format!("dp6_geq_dp{i}"),
            &format!("dp.index(6) >= dp.index({i})"),
        );
    }

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75c: LIS length should equal max dp value, got: {:?}",
        result,
    );
}

/// Tier 75c: the witness subsequence [2, 3, 7, 8] is strictly increasing.
#[test]
fn test_vt_tier75c_witness_is_strictly_increasing() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("witness_len", "witness_val.len() == 4");
    ctx.push_assert("w01_inc", "witness_val.index(0) < witness_val.index(1)");
    ctx.push_assert("w12_inc", "witness_val.index(1) < witness_val.index(2)");
    ctx.push_assert("w23_inc", "witness_val.index(2) < witness_val.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75c: witness subsequence should be strictly increasing, got: {:?}",
        result,
    );
}

/// Tier 75c: witness indices are strictly increasing and values match `a`.
#[test]
fn test_vt_tier75c_witness_indices_valid_and_values_match() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    // Indices are strictly increasing
    ctx.push_assert("idx_01", "witness_idx.index(0) < witness_idx.index(1)");
    ctx.push_assert("idx_12", "witness_idx.index(1) < witness_idx.index(2)");
    ctx.push_assert("idx_23", "witness_idx.index(2) < witness_idx.index(3)");
    // Values match `a` at the given indices
    ctx.push_assert(
        "val_0",
        "witness_val.index(0) == a.index(witness_idx.index(0))",
    );
    ctx.push_assert(
        "val_1",
        "witness_val.index(1) == a.index(witness_idx.index(1))",
    );
    ctx.push_assert(
        "val_2",
        "witness_val.index(2) == a.index(witness_idx.index(2))",
    );
    ctx.push_assert(
        "val_3",
        "witness_val.index(3) == a.index(witness_idx.index(3))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75c: witness indices and values should be valid, got: {:?}",
        result,
    );
}

/// Tier 75c: witness length matches the LIS length and dp at the final witness index.
#[test]
fn test_vt_tier75c_witness_length_matches_dp_at_endpoint() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("witness_len_is_4", "witness_val.len() == 4");
    ctx.push_assert(
        "dp_at_endpoint_matches",
        "dp.index(witness_idx.index(3)) == witness_val.len()",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 75c: witness length should match dp at its endpoint, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 75d NEGATIVE: dp[4] cannot be 2, it must be 1 (no predecessor with a[j] < 1).
#[test]
fn test_vt_tier75d_inflated_dp_at_base_case_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    ctx.push_assert("dp4_is_two", "dp.index(4) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 75d SOUNDNESS: inflated dp at base-case index should be rejected, got: {:?}",
        result,
    );
}

/// Tier 75d NEGATIVE: claiming the LIS length is 5 (exceeds max dp) is unsound.
#[test]
fn test_vt_tier75d_lis_exceeds_max_dp_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);
    ctx.declare_var_parsed("lis_len", "u64");
    ctx.push_assume("lis_len_val", "lis_len == 5");

    // This should fail because max(dp) = 4, not 5
    ctx.push_assert("lis_matches_some_dp", "lis_len == dp.index(6)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 75d SOUNDNESS: LIS length exceeding max dp should be rejected, got: {:?}",
        result,
    );
}

/// Tier 75d NEGATIVE: a non-increasing witness [2, 3, 7, 4] fails the subsequence test.
#[test]
fn test_vt_tier75d_non_increasing_witness_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_lis_example(&mut ctx);

    // The bad witness has 7 > 4 at the end
    ctx.declare_var_parsed("bad_w2", "u64");
    ctx.declare_var_parsed("bad_w3", "u64");
    ctx.push_assume("bad_w2_val", "bad_w2 == 7");
    ctx.push_assume("bad_w3_val", "bad_w3 == 4");

    ctx.push_assert("bad_w2_lt_bad_w3", "bad_w2 < bad_w3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 75d SOUNDNESS: non-increasing witness should be rejected, got: {:?}",
        result,
    );
}
