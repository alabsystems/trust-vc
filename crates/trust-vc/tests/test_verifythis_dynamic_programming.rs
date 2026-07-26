// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 52 — Dynamic Programming VCs.
//!
//! DP problems are common in VerifyThis (edit distance, LCS, optimal
//! partitioning). The core verification pattern decomposes into:
//!   1. Base case (Init): dp[0], dp[1] satisfy boundary definitions
//!   2. Inductive step (Step): dp[i] = f(dp[i-1], dp[i-2], ...) under IH
//!   3. Postcondition (Exit): dp[n-1] satisfies the problem's answer spec
//!
//! Three DP families covered:
//!   A. Fibonacci recurrence — dp[i] = dp[i-1] + dp[i-2]
//!   B. Min-cost staircase — dp[i] = cost[i] + min(dp[i-1], dp[i-2])
//!   C. Max non-adjacent sum — dp[i] = max(dp[i-1], dp[i-2] + s[i])
//!
//! GROUP A: Fibonacci   B: Min-cost   C: Max non-adjacent   D: Negatives
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

// ========================================================================
// GROUP A: Fibonacci recurrence — dp[i] = dp[i-1] + dp[i-2]
// ========================================================================

/// Tier 52a: Init — dp[0] = 0, dp[1] = 1 satisfy base cases.
#[test]
fn test_vt_tier52a_fibonacci_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dp", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "dp.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("base0", "dp.index(0) == 0");
    ctx.push_assume("base1", "dp.index(1) == 1");

    // Base cases: dp[0] >= 0 and dp[1] >= 0
    ctx.push_assert("base0_nonneg", "dp.index(0) >= 0");
    ctx.push_assert("base1_nonneg", "dp.index(1) >= 0");
    // dp[1] >= dp[0] (monotonicity from index 1)
    ctx.push_assert("mono_01", "dp.index(1) >= dp.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52a: fibonacci init should verify, got: {:?}",
        result,
    );
}

/// Tier 52a: Step — assuming dp[i-1], dp[i-2] >= 0 and dp[i] = dp[i-1] + dp[i-2],
/// then dp[i] >= 0 and dp[i] >= dp[i-1].
#[test]
fn test_vt_tier52a_fibonacci_step_nonneg_and_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dp_im2", "i64"); // dp[i-2]
    ctx.declare_var_parsed("dp_im1", "i64"); // dp[i-1]
    ctx.declare_var_parsed("dp_i", "i64"); // dp[i]

    // IH: prior elements are non-negative and bounded (BV64 overflow guard)
    ctx.push_assume("ih_im2_nonneg", "dp_im2 >= 0");
    ctx.push_assume("ih_im1_nonneg", "dp_im1 >= 0");
    ctx.push_assume("ih_im2_bounded", "dp_im2 < 1000000");
    ctx.push_assume("ih_im1_bounded", "dp_im1 < 1000000");
    // IH: monotonicity dp[i-1] >= dp[i-2]
    ctx.push_assume("ih_mono", "dp_im1 >= dp_im2");
    // Recurrence
    ctx.push_assume("recurrence", "dp_i == dp_im1 + dp_im2");

    // dp[i] >= 0
    ctx.push_assert("nonneg", "dp_i >= 0");
    // dp[i] >= dp[i-1] (monotonicity preserved)
    ctx.push_assert("monotone", "dp_i >= dp_im1");
    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52a: fibonacci step should verify, got: {:?}",
        result,
    );
}

/// Tier 52a: Concrete trace — fib(0..7) = [0, 1, 1, 2, 3, 5, 8].
/// Verifies recurrence, monotonicity, and non-negativity over full table.
#[test]
fn test_vt_tier52a_fibonacci_concrete_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dp", &[0, 1, 1, 2, 3, 5, 8]);

    // Recurrence holds at every position
    ctx.push_assert("rec2", "dp.index(2) == dp.index(1) + dp.index(0)");
    ctx.push_assert("rec3", "dp.index(3) == dp.index(2) + dp.index(1)");
    ctx.push_assert("rec4", "dp.index(4) == dp.index(3) + dp.index(2)");
    ctx.push_assert("rec5", "dp.index(5) == dp.index(4) + dp.index(3)");
    ctx.push_assert("rec6", "dp.index(6) == dp.index(5) + dp.index(4)");
    // All non-negative
    ctx.push_assert(
        "all_nonneg",
        "forall(|k: u64| !(k < 7) || dp.index(k) >= 0)",
    );
    // Monotone from index 1
    ctx.push_assert("mono12", "dp.index(2) >= dp.index(1)");
    ctx.push_assert("mono56", "dp.index(6) >= dp.index(5)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52a: fibonacci concrete trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Min-cost staircase — dp[i] = cost[i] + min(dp[i-1], dp[i-2])
// ========================================================================

/// Tier 52b: Init — dp[0] = cost[0], dp[1] = cost[1].
/// Each dp[i] >= cost[i] (can't do better than the step itself).
#[test]
fn test_vt_tier52b_mincost_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cost", "Seq<i64>");
    ctx.declare_var_parsed("dp", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_cost", "cost.len() == n");
    ctx.push_assume("len_dp", "dp.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_bounded", "n < 1000000");
    // All costs are non-negative
    ctx.push_assume(
        "costs_nonneg",
        "forall(|k: u64| !(k < n) || cost.index(k) >= 0)",
    );
    // Base cases
    ctx.push_assume("base0", "dp.index(0) == cost.index(0)");
    ctx.push_assume("base1", "dp.index(1) == cost.index(1)");

    // dp[i] >= cost[i] for base cases
    ctx.push_assert("dp0_ge_cost0", "dp.index(0) >= cost.index(0)");
    ctx.push_assert("dp1_ge_cost1", "dp.index(1) >= cost.index(1)");
    // dp[i] >= 0 for base cases
    ctx.push_assert("dp0_nonneg", "dp.index(0) >= 0");
    ctx.push_assert("dp1_nonneg", "dp.index(1) >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52b: mincost init should verify, got: {:?}",
        result,
    );
}

/// Tier 52b: Step — dp[i] = cost[i] + min(dp[i-1], dp[i-2]).
/// Proves: dp[i] <= cost[i] + dp[i-1] AND dp[i] <= cost[i] + dp[i-2].
/// This is the optimality substructure: dp[i] is at most as costly as
/// either single-step predecessor path.
#[test]
fn test_vt_tier52b_mincost_step_optimality() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cost_i", "i64");
    ctx.declare_var_parsed("dp_im2", "i64");
    ctx.declare_var_parsed("dp_im1", "i64");
    ctx.declare_var_parsed("dp_i", "i64");

    ctx.push_assume("cost_nonneg", "cost_i >= 0");
    ctx.push_assume("cost_bounded", "cost_i < 1000000");
    ctx.push_assume("ih_im2_nonneg", "dp_im2 >= 0");
    ctx.push_assume("ih_im1_nonneg", "dp_im1 >= 0");
    ctx.push_assume("ih_im2_bounded", "dp_im2 < 1000000");
    ctx.push_assume("ih_im1_bounded", "dp_im1 < 1000000");
    // Recurrence: dp[i] = cost[i] + min(dp[i-1], dp[i-2])
    // Encoded as: dp[i] == cost[i] + (if dp[i-1] < dp[i-2] then dp[i-1] else dp[i-2])
    ctx.push_assume(
        "recurrence",
        "dp_i == cost_i + if dp_im1 < dp_im2 { dp_im1 } else { dp_im2 }",
    );

    // Optimality: dp[i] is no worse than either predecessor path
    ctx.push_assert("opt_via_im1", "dp_i <= cost_i + dp_im1");
    ctx.push_assert("opt_via_im2", "dp_i <= cost_i + dp_im2");
    // Non-negativity preserved
    ctx.push_assert("nonneg", "dp_i >= 0");
    // dp[i] >= cost[i] (can't do better than step cost alone)
    ctx.push_assert("ge_cost", "dp_i >= cost_i");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52b: mincost step optimality should verify, got: {:?}",
        result,
    );
}

/// Tier 52b: Concrete trace — cost = [1, 3, 2, 4, 1], dp = [1, 3, 3, 7, 4].
/// dp[2] = 2 + min(3, 1) = 3, dp[3] = 4 + min(3, 3) = 7, dp[4] = 1 + min(7, 3) = 4.
#[test]
fn test_vt_tier52b_mincost_concrete_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "cost", &[1, 3, 2, 4, 1]);
    assume_seq_i64(&mut ctx, "dp", &[1, 3, 3, 7, 4]);

    // Base cases
    ctx.push_assert("base0", "dp.index(0) == cost.index(0)");
    ctx.push_assert("base1", "dp.index(1) == cost.index(1)");
    // Recurrence at each step (unrolled min)
    // dp[2] = cost[2] + min(dp[1], dp[0]) = 2 + min(3, 1) = 2 + 1 = 3
    ctx.push_assert(
        "rec2",
        "dp.index(2) == cost.index(2) + if dp.index(1) < dp.index(0) { dp.index(1) } else { dp.index(0) }",
    );
    // dp[3] = cost[3] + min(dp[2], dp[1]) = 4 + min(3, 3) = 4 + 3 = 7
    ctx.push_assert(
        "rec3",
        "dp.index(3) == cost.index(3) + if dp.index(2) < dp.index(1) { dp.index(2) } else { dp.index(1) }",
    );
    // dp[4] = cost[4] + min(dp[3], dp[2]) = 1 + min(7, 3) = 1 + 3 = 4
    ctx.push_assert(
        "rec4",
        "dp.index(4) == cost.index(4) + if dp.index(3) < dp.index(2) { dp.index(3) } else { dp.index(2) }",
    );
    // Optimality at exit: dp[4] <= cost[4] + dp[3] AND dp[4] <= cost[4] + dp[2]
    ctx.push_assert("opt4_via3", "dp.index(4) <= cost.index(4) + dp.index(3)");
    ctx.push_assert("opt4_via2", "dp.index(4) <= cost.index(4) + dp.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52b: mincost concrete trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Max non-adjacent sum — dp[i] = max(dp[i-1], dp[i-2] + s[i])
// ========================================================================

/// Tier 52c: Init — dp[0] = max(0, s[0]), dp[1] = max(dp[0], s[1]).
#[test]
fn test_vt_tier52c_max_nonadj_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s0", "i64");
    ctx.declare_var_parsed("s1", "i64");
    ctx.declare_var_parsed("dp0", "i64");
    ctx.declare_var_parsed("dp1", "i64");

    // dp[0] = max(0, s[0])
    ctx.push_assume("base0", "dp0 == if s0 > 0 { s0 } else { 0 }");
    // dp[1] = max(dp[0], s[1])
    ctx.push_assume("base1", "dp1 == if s1 > dp0 { s1 } else { dp0 }");

    // dp[0] >= 0
    ctx.push_assert("dp0_nonneg", "dp0 >= 0");
    // dp[1] >= dp[0] (monotonically non-decreasing)
    ctx.push_assert("dp1_ge_dp0", "dp1 >= dp0");
    // dp[1] >= 0
    ctx.push_assert("dp1_nonneg", "dp1 >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52c: max non-adjacent init should verify, got: {:?}",
        result,
    );
}

/// Tier 52c: Step — dp[i] = max(dp[i-1], dp[i-2] + s[i]).
/// Proves dp[i] >= dp[i-1] (monotone) and dp[i] >= dp[i-2] + s[i].
#[test]
fn test_vt_tier52c_max_nonadj_step_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s_i", "i64");
    ctx.declare_var_parsed("dp_im2", "i64");
    ctx.declare_var_parsed("dp_im1", "i64");
    ctx.declare_var_parsed("dp_i", "i64");

    ctx.push_assume("s_i_nonneg", "s_i >= 0");
    ctx.push_assume("s_i_bounded", "s_i < 1000000");
    ctx.push_assume("ih_im2_nonneg", "dp_im2 >= 0");
    ctx.push_assume("ih_im1_nonneg", "dp_im1 >= 0");
    ctx.push_assume("ih_im2_bounded", "dp_im2 < 1000000");
    ctx.push_assume("ih_im1_bounded", "dp_im1 < 1000000");
    ctx.push_assume("ih_mono", "dp_im1 >= dp_im2");
    // Recurrence: dp[i] = max(dp[i-1], dp[i-2] + s[i])
    ctx.push_assume(
        "recurrence",
        "dp_i == if dp_im2 + s_i > dp_im1 { dp_im2 + s_i } else { dp_im1 }",
    );

    // Monotonicity: dp[i] >= dp[i-1]
    ctx.push_assert("monotone", "dp_i >= dp_im1");
    // dp[i] >= dp[i-2] (from monotonicity chain: dp[i] >= dp[i-1] >= dp[i-2])
    ctx.push_assert("ge_im2", "dp_i >= dp_im2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52c: max non-adjacent step should verify, got: {:?}",
        result,
    );
}

/// Tier 52c: Concrete trace — s = [3, 2, 7, 10], dp = [3, 3, 10, 13].
/// dp[0] = max(0, 3) = 3, dp[1] = max(3, 2) = 3,
/// dp[2] = max(3, 0+7) = max(3, 7) = 7... wait, dp[2] = max(dp[1], dp[0]+s[2]).
/// dp[2] = max(3, 3+7) = max(3, 10) = 10.
/// dp[3] = max(10, 3+10) = max(10, 13) = 13.
/// Optimal selection: s[2]+s[3] via non-adjacent? No: s[0]+s[2] = 10 or s[0]+s[3] = 13.
/// Actually dp[3] = max(dp[2], dp[1]+s[3]) = max(10, 3+10) = 13. Selects {s[0], s[3]}.
#[test]
fn test_vt_tier52c_max_nonadj_concrete_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[3, 2, 7, 10]);
    assume_seq_i64(&mut ctx, "dp", &[3, 3, 10, 13]);

    // Base cases
    ctx.push_assert(
        "base0",
        "dp.index(0) == if s.index(0) > 0 { s.index(0) } else { 0 }",
    );
    ctx.push_assert(
        "base1",
        "dp.index(1) == if s.index(1) > dp.index(0) { s.index(1) } else { dp.index(0) }",
    );
    // Recurrence
    ctx.push_assert(
        "rec2",
        "dp.index(2) == if dp.index(0) + s.index(2) > dp.index(1) { dp.index(0) + s.index(2) } else { dp.index(1) }",
    );
    ctx.push_assert(
        "rec3",
        "dp.index(3) == if dp.index(1) + s.index(3) > dp.index(2) { dp.index(1) + s.index(3) } else { dp.index(2) }",
    );
    // Monotonicity across all positions
    ctx.push_assert("mono01", "dp.index(1) >= dp.index(0)");
    ctx.push_assert("mono12", "dp.index(2) >= dp.index(1)");
    ctx.push_assert("mono23", "dp.index(3) >= dp.index(2)");
    // Final answer: dp[3] == 13 == s[0] + s[3] = 3 + 10
    ctx.push_assert("answer", "dp.index(3) == s.index(0) + s.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 52c: max non-adjacent concrete trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 52d NEGATIVE: Wrong Fibonacci base case — dp[0] = 1 instead of 0.
/// Monotonicity dp[1] >= dp[0] still holds, but dp[2] = dp[1] + dp[0] = 2
/// while the correct fib(2) = 1. Asserting dp[2] == 1 should fail.
#[test]
fn test_vt_tier52d_wrong_fib_base_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "dp", &[1, 1, 2, 3, 5]);

    // Recurrence still holds with wrong base
    ctx.push_assert("rec2_holds", "dp.index(2) == dp.index(1) + dp.index(0)");

    // But claiming this is the standard Fibonacci (where fib(2) = 1) fails
    ctx.push_assert("wrong_fib2", "dp.index(2) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 52d SOUNDNESS: wrong fib base should reject fib(2)==1, got: {:?}",
        result,
    );
}

/// Tier 52d NEGATIVE: Wrong min-cost recurrence — using max instead of min.
/// dp[i] = cost[i] + max(dp[i-1], dp[i-2]) gives WORST path, not best.
/// Claiming dp[i] <= cost[i] + dp[i-2] should fail when dp[i-1] > dp[i-2].
#[test]
fn test_vt_tier52d_wrong_mincost_recurrence_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cost_i", "i64");
    ctx.declare_var_parsed("dp_im2", "i64");
    ctx.declare_var_parsed("dp_im1", "i64");
    ctx.declare_var_parsed("dp_i", "i64");

    ctx.push_assume("cost_nonneg", "cost_i >= 0");
    ctx.push_assume("ih_im2_nonneg", "dp_im2 >= 0");
    ctx.push_assume("ih_im1_nonneg", "dp_im1 >= 0");
    // WRONG: using max instead of min
    ctx.push_assume(
        "wrong_recurrence",
        "dp_i == cost_i + if dp_im1 > dp_im2 { dp_im1 } else { dp_im2 }",
    );

    // This optimality claim is valid for min but NOT for max
    ctx.push_assert("wrong_opt", "dp_i <= cost_i + dp_im2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 52d SOUNDNESS: max-recurrence should reject min-optimality, got: {:?}",
        result,
    );
}

/// Tier 52d NEGATIVE: Non-adjacent sum with wrong recurrence — using dp[i-1]
/// instead of dp[i-2] in the "take" branch allows adjacent selection.
/// dp[i] = max(dp[i-1], dp[i-1] + s[i]) = dp[i-1] + max(0, s[i]).
/// Claiming dp[n-1] comes from non-adjacent elements should fail.
#[test]
fn test_vt_tier52d_adjacent_selection_negative() {
    let mut ctx = VerificationContext::new();
    // s = [5, 5], correct non-adj dp = [5, 5], wrong dp = [5, 10]
    assume_seq_i64(&mut ctx, "s", &[5, 5]);

    ctx.declare_var_parsed("dp_wrong", "Seq<i64>");
    ctx.push_assume("dw_len", "dp_wrong.len() == 2");
    ctx.push_assume("dw_0", "dp_wrong.index(0) == 5");
    // WRONG: dp[1] = dp[0] + s[1] = 10 (adjacent selection)
    ctx.push_assume("dw_1", "dp_wrong.index(1) == 10");

    // Correct non-adjacent answer for [5, 5] is max(5, 5) = 5, not 10
    // Claiming dp[1] <= max individual element should fail
    ctx.push_assert(
        "wrong_bound",
        "dp_wrong.index(1) <= s.index(0) || dp_wrong.index(1) <= s.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 52d SOUNDNESS: adjacent selection should reject bound, got: {:?}",
        result,
    );
}
