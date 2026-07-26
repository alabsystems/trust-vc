// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 31 - Sliding-window VCs.
//!
//! Sliding-window algorithms appear in VerifyThis-style tasks:
//!   - smallest subarray with sum >= target
//!   - fixed-length max/average windows
//!   - amortized two-pointer scans over contiguous intervals
//!
//! The core proof obligations are:
//!   1. rolling-sum updates when the window shifts
//!   2. expand/shrink step monotonicity
//!   3. direction-sensitive negatives (removing the wrong endpoint is unsound)
//!
//! KEY LESSON: encoding the rolling-sum relation explicitly as
//! `sum_new == sum - old + new` gives ay the right algebraic shape without
//! introducing heavier slice-sum axioms.
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
// GROUP A: Fixed-size rolling windows
// ========================================================================

/// Tier 31a: shifting a length-3 window right preserves the rolling sum.
///
/// Old window: indices [1, 4) -> s[1] + s[2] + s[3]
/// New window: indices [2, 5) -> s[2] + s[3] + s[4]
#[test]
fn test_vt_tier31a_fixed_window_shift_preserves_rolling_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("lo_new", "u64");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("lo_is_1", "lo == 1");
    ctx.push_assume(
        "e1_bound",
        "s.index(1) >= -1000000 && s.index(1) <= 1000000",
    );
    ctx.push_assume(
        "e2_bound",
        "s.index(2) >= -1000000 && s.index(2) <= 1000000",
    );
    ctx.push_assume(
        "e3_bound",
        "s.index(3) >= -1000000 && s.index(3) <= 1000000",
    );
    ctx.push_assume(
        "e4_bound",
        "s.index(4) >= -1000000 && s.index(4) <= 1000000",
    );
    ctx.push_assume("sum_def", "sum == s.index(1) + s.index(2) + s.index(3)");
    ctx.push_assume("lo_step", "lo_new == lo + 1");
    ctx.push_assume("sum_step", "sum_new == sum - s.index(1) + s.index(4)");

    ctx.push_assert("lo_new_two", "lo_new == 2");
    ctx.push_assert(
        "rolling_sum",
        "sum_new == s.index(2) + s.index(3) + s.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 31a: fixed-window rolling sum should verify, got: {:?}",
        result,
    );
}

/// Tier 31b: once a non-negative window is over budget, expanding cannot fix it.
///
/// Competition pattern: smallest-subarray and bounded-window scans only shrink
/// after the running sum crosses the limit. This checks that adding another
/// non-negative element preserves the `sum > limit` condition.
#[test]
fn test_vt_tier31b_expand_nonnegative_window_stays_over_budget() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");
    ctx.declare_var_parsed("limit", "i32");

    ctx.push_assume("len4", "s.len() == 4");
    ctx.push_assume("sum_bound", "sum >= -1000000 && sum <= 1000000");
    ctx.push_assume("limit_bound", "limit >= -1000000 && limit <= 1000000");
    ctx.push_assume(
        "new_nonnegative",
        "s.index(2) >= 0 && s.index(2) <= 1000000",
    );
    ctx.push_assume("already_over", "sum > limit");
    ctx.push_assume("sum_step", "sum_new == sum + s.index(2)");

    ctx.push_assert("still_over", "sum_new > limit");
    ctx.push_assert("monotone", "sum_new >= sum");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 31b: expanding an over-budget non-negative window should verify, got: {:?}",
        result,
    );
}

/// Tier 31c: shrinking from the left drops exactly the outgoing element.
#[test]
fn test_vt_tier31c_shrink_left_restores_suffix_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("lo_new", "u64");
    ctx.declare_var_parsed("hi", "u64");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("lo_is_1", "lo == 1");
    ctx.push_assume("hi_is_4", "hi == 4");
    ctx.push_assume(
        "e1_bound",
        "s.index(1) >= -1000000 && s.index(1) <= 1000000",
    );
    ctx.push_assume(
        "e2_bound",
        "s.index(2) >= -1000000 && s.index(2) <= 1000000",
    );
    ctx.push_assume(
        "e3_bound",
        "s.index(3) >= -1000000 && s.index(3) <= 1000000",
    );
    ctx.push_assume("sum_def", "sum == s.index(1) + s.index(2) + s.index(3)");
    ctx.push_assume("lo_step", "lo_new == lo + 1");
    ctx.push_assume("sum_step", "sum_new == sum - s.index(1)");

    ctx.push_assert("lo_new_lt_hi", "lo_new < hi");
    ctx.push_assert("suffix_sum", "sum_new == s.index(2) + s.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 31c: shrinking from the left should preserve the suffix sum, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Concrete practice trace
// ========================================================================

/// Tier 31d: expand-then-shrink trace for a budgeted window.
///
/// Sequence: [2, 1, 3, 2, 1], limit = 5
///   start  [0, 2): sum = 3
///   expand [0, 3): sum = 6  (> limit)
///   shrink [1, 3): sum = 4  (<= limit)
#[test]
fn test_vt_tier31d_expand_then_shrink_trace() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("limit", "i32");
    ctx.declare_var_parsed("lo0", "u64");
    ctx.declare_var_parsed("hi0", "u64");
    ctx.declare_var_parsed("hi1", "u64");
    ctx.declare_var_parsed("lo2", "u64");
    ctx.declare_var_parsed("sum0", "i32");
    ctx.declare_var_parsed("sum1", "i32");
    ctx.declare_var_parsed("sum2", "i32");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("s0", "s.index(0) == 2");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 3");
    ctx.push_assume("s3", "s.index(3) == 2");
    ctx.push_assume("s4", "s.index(4) == 1");
    ctx.push_assume("limit5", "limit == 5");
    ctx.push_assume("lo0_init", "lo0 == 0");
    ctx.push_assume("hi0_init", "hi0 == 2");
    ctx.push_assume("sum0_def", "sum0 == s.index(0) + s.index(1)");
    ctx.push_assume("hi1_step", "hi1 == hi0 + 1");
    ctx.push_assume("sum1_step", "sum1 == sum0 + s.index(2)");
    ctx.push_assume("lo2_step", "lo2 == lo0 + 1");
    ctx.push_assume("sum2_step", "sum2 == sum1 - s.index(0)");

    ctx.push_assert("sum0_three", "sum0 == 3");
    ctx.push_assert("hi1_three", "hi1 == 3");
    ctx.push_assert("sum1_six", "sum1 == 6");
    ctx.push_assert("sum1_over", "sum1 > limit");
    ctx.push_assert("lo2_one", "lo2 == 1");
    ctx.push_assert("sum2_four", "sum2 == 4");
    ctx.push_assert("sum2_fits", "sum2 <= limit");
    ctx.push_assert("sum2_window", "sum2 == s.index(1) + s.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 31d: concrete expand-then-shrink trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 31e: a shifted window must not keep the outgoing element in its sum.
#[test]
fn test_vt_tier31e_wrong_rolling_sum_candidate_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 4");
    ctx.push_assume("s3", "s.index(3) == 6");
    ctx.push_assume("s4", "s.index(4) == 10");
    ctx.push_assume("sum_def", "sum == s.index(1) + s.index(2) + s.index(3)");
    ctx.push_assume("sum_step", "sum_new == sum - s.index(1) + s.index(4)");

    ctx.push_assert(
        "wrong_window",
        "sum_new == s.index(1) + s.index(2) + s.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 31e SOUNDNESS: shifted window must reject the wrong sum, got: {:?}",
        result,
    );
}

/// Tier 31f: removing the right endpoint is not the same as shrinking left.
#[test]
fn test_vt_tier31f_shrink_right_is_not_left_shrink() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("hi_new", "u64");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("lo_is_1", "lo == 1");
    ctx.push_assume("hi_is_4", "hi == 4");
    ctx.push_assume("s1", "s.index(1) == 4");
    ctx.push_assume("s2", "s.index(2) == 5");
    ctx.push_assume("s3", "s.index(3) == 7");
    ctx.push_assume("sum_def", "sum == s.index(1) + s.index(2) + s.index(3)");
    ctx.push_assume("hi_step", "hi_new == hi - 1");
    ctx.push_assume("sum_step", "sum_new == sum - s.index(3)");

    ctx.push_assert("hi_new_three", "hi_new == 3");
    ctx.push_assert("wrong_left_shrink", "sum_new == s.index(2) + s.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 31f SOUNDNESS: shrinking right must not verify as a left-shrink step, got: {:?}",
        result,
    );
}
