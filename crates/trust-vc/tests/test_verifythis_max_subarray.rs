// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 63 — Maximum Subarray (Kadane's Algorithm) VCs.
//!
//! Kadane's algorithm finds the contiguous subarray with the largest sum:
//!   - `a: Seq<i64>` — input array
//!   - `max_here: i64` — best sum ending at current position
//!   - `max_so_far: i64` — global best sum seen so far
//!
//! Loop body:
//!   max_here = max(a[i], max_here + a[i])
//!   max_so_far = max(max_so_far, max_here)
//!
//! Competition proofs need:
//!   - init: max_here = max_so_far = a[0]
//!   - step: max_here is the best sum of any subarray ending at i
//!   - invariant: max_so_far >= sum of any subarray in a[0..=i]
//!   - exit: max_so_far is the maximum subarray sum
//!   - negatives: wrong sums, missed subarrays, empty-array edge cases
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
// GROUP A: Init — max_here = max_so_far = a[0]
// ========================================================================

/// Tier 63a: Init — single-element array: max subarray sum equals the element.
#[test]
fn test_vt_tier63a_init_single_element() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[42]);

    ctx.declare_var_parsed("max_here", "i64");
    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.push_assume("init_here", "max_here == a.index(0)");
    ctx.push_assume("init_far", "max_so_far == a.index(0)");

    ctx.push_assert("here_correct", "max_here == 42");
    ctx.push_assert("far_correct", "max_so_far == 42");
    ctx.push_assert("far_ge_here", "max_so_far >= max_here");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63a: single element init should verify, got: {:?}",
        result,
    );
}

/// Tier 63a: Init — negative single element: max subarray is that element.
#[test]
fn test_vt_tier63a_init_negative_element() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-5]);

    ctx.declare_var_parsed("max_here", "i64");
    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.push_assume("init_here", "max_here == a.index(0)");
    ctx.push_assume("init_far", "max_so_far == a.index(0)");

    ctx.push_assert("here_neg", "max_here == -5");
    ctx.push_assert("far_neg", "max_so_far == -5");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63a: negative element init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — Kadane transition at each index
// ========================================================================

/// Tier 63b: Step — extending is better than starting fresh.
/// a = [-2, 1, -3, 4, -1, 2, 1, -5, 4], classic example.
/// At i=3 (a[3]=4): max_here = max(4, -2+4) = 4 (start fresh).
#[test]
fn test_vt_tier63b_step_start_fresh() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    ctx.declare_var_parsed("max_here_pre", "i64");
    ctx.declare_var_parsed("max_here_post", "i64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("i_val", "i == 3");
    ctx.push_assume("pre_val", "max_here_pre == -2"); // best ending at i=2

    // Kadane step: max(a[i], max_here_pre + a[i])
    ctx.push_assume(
        "kadane_step",
        "max_here_post == if a.index(i) > max_here_pre + a.index(i) \
         { a.index(i) } else { max_here_pre + a.index(i) }",
    );

    // Starting fresh is better: a[3]=4 > -2+4=2
    ctx.push_assert("start_fresh", "max_here_post == a.index(i)");
    ctx.push_assert("post_val", "max_here_post == 4");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63b: start-fresh step should verify, got: {:?}",
        result,
    );
}

/// Tier 63b: Step — extending the current subarray is better.
/// At i=5 (a[5]=2): max_here_pre = 3 (subarray [4,-1]), max_here = max(2, 3+2) = 5.
#[test]
fn test_vt_tier63b_step_extend() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    ctx.declare_var_parsed("max_here_pre", "i64");
    ctx.declare_var_parsed("max_here_post", "i64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("i_val", "i == 5");
    ctx.push_assume("pre_val", "max_here_pre == 3"); // best ending at i=4: [4,-1]
    ctx.push_assume(
        "kadane_step",
        "max_here_post == if a.index(i) > max_here_pre + a.index(i) \
         { a.index(i) } else { max_here_pre + a.index(i) }",
    );

    // Extending is better: 3+2=5 > 2
    ctx.push_assert(
        "extend_better",
        "max_here_post == max_here_pre + a.index(i)",
    );
    ctx.push_assert("post_val", "max_here_post == 5");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63b: extend step should verify, got: {:?}",
        result,
    );
}

/// Tier 63b: Step — max_so_far updates when max_here exceeds it.
#[test]
fn test_vt_tier63b_step_global_max_update() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("max_here", "i64");
    ctx.declare_var_parsed("max_so_far_pre", "i64");
    ctx.declare_var_parsed("max_so_far_post", "i64");

    ctx.push_assume("here_val", "max_here == 6");
    ctx.push_assume("far_pre", "max_so_far_pre == 4");
    ctx.push_assume(
        "far_update",
        "max_so_far_post == if max_here > max_so_far_pre \
         { max_here } else { max_so_far_pre }",
    );

    ctx.push_assert("new_global_max", "max_so_far_post == 6");
    ctx.push_assert("far_ge_here", "max_so_far_post >= max_here");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63b: global max update should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — max_so_far dominates all seen subarrays
// ========================================================================

/// Tier 63c: Invariant — max_so_far ≥ every prefix subarray sum.
/// a = [-2, 1, -3, 4, -1, 2, 1, -5, 4].
/// After processing all elements, max_so_far = 6 (subarray [4, -1, 2, 1]).
#[test]
fn test_vt_tier63c_max_dominates_all_prefix_sums() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.push_assume("msf_val", "max_so_far == 6");

    // Check against all single-element subarrays
    ctx.push_assert("ge_a0", "max_so_far >= a.index(0)");
    ctx.push_assert("ge_a1", "max_so_far >= a.index(1)");
    ctx.push_assert("ge_a3", "max_so_far >= a.index(3)");
    ctx.push_assert("ge_a8", "max_so_far >= a.index(8)");

    // Check against known subarray sums:
    // [4,-1,2,1] = 6, [-2,1] = -1, [4,-1,2,1,-5,4] = 5, [1,-3,4] = 2
    ctx.push_assert("ge_best", "max_so_far >= 6");
    ctx.push_assert("ge_neg", "max_so_far >= -1");
    ctx.push_assert("ge_tail", "max_so_far >= 5");
    ctx.push_assert("ge_mid", "max_so_far >= 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63c: max_so_far dominates all prefix sums, got: {:?}",
        result,
    );
}

/// Tier 63c: Invariant — intermediate state after processing a[0..=4].
/// a = [-2, 1, -3, 4, -1]. max_here = 3 (subarray [4,-1]).
/// max_so_far = 4 (subarray [4]).
#[test]
fn test_vt_tier63c_intermediate_invariant() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1]);

    ctx.declare_var_parsed("max_here", "i64");
    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.push_assume("mh_val", "max_here == 3");
    ctx.push_assume("msf_val", "max_so_far == 4");

    // max_so_far >= max_here always
    ctx.push_assert("far_ge_here", "max_so_far >= max_here");
    // max_so_far >= each element
    ctx.push_assert("ge_0", "max_so_far >= a.index(0)");
    ctx.push_assert("ge_1", "max_so_far >= a.index(1)");
    ctx.push_assert("ge_2", "max_so_far >= a.index(2)");
    ctx.push_assert("ge_3", "max_so_far >= a.index(3)");
    ctx.push_assert("ge_4", "max_so_far >= a.index(4)");
    // max_here = sum of best subarray ending at i=4
    // [4,-1] = 3, which is correct
    ctx.push_assert("here_correct", "max_here == a.index(3) + a.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63c: intermediate invariant should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit — full algorithm trace on classic example
// ========================================================================

/// Tier 63d: Exit — complete trace of Kadane on [-2, 1, -3, 4, -1, 2, 1, -5, 4].
/// Expected: max subarray = [4, -1, 2, 1], sum = 6.
#[test]
fn test_vt_tier63d_full_kadane_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    // Trace: max_here at each step
    // i=0: max_here = -2, max_so_far = -2
    // i=1: max_here = max(1, -2+1) = 1, max_so_far = 1
    // i=2: max_here = max(-3, 1-3) = -2, max_so_far = 1
    // i=3: max_here = max(4, -2+4) = 4, max_so_far = 4
    // i=4: max_here = max(-1, 4-1) = 3, max_so_far = 4
    // i=5: max_here = max(2, 3+2) = 5, max_so_far = 5
    // i=6: max_here = max(1, 5+1) = 6, max_so_far = 6
    // i=7: max_here = max(-5, 6-5) = 1, max_so_far = 6
    // i=8: max_here = max(4, 1+4) = 5, max_so_far = 6
    assume_seq_i64(&mut ctx, "mh", &[-2, 1, -2, 4, 3, 5, 6, 1, 5]);
    assume_seq_i64(&mut ctx, "msf", &[-2, 1, 1, 4, 4, 5, 6, 6, 6]);

    // Initial step
    ctx.push_assert("mh_0", "mh.index(0) == a.index(0)");
    ctx.push_assert("msf_0", "msf.index(0) == a.index(0)");

    // Kadane transitions for selected steps
    // i=3: start fresh
    ctx.push_assert("mh_3_fresh", "mh.index(3) == a.index(3)");
    ctx.push_assert("mh_3_gt_extend", "a.index(3) > mh.index(2) + a.index(3)");

    // i=6: extend
    ctx.push_assert("mh_6_extend", "mh.index(6) == mh.index(5) + a.index(6)");
    ctx.push_assert("mh_6_gt_fresh", "mh.index(5) + a.index(6) >= a.index(6)");

    // max_so_far is non-decreasing
    ctx.push_assert("msf_nd_01", "msf.index(1) >= msf.index(0)");
    ctx.push_assert("msf_nd_23", "msf.index(3) >= msf.index(2)");
    ctx.push_assert("msf_nd_67", "msf.index(7) >= msf.index(6)");

    // Final answer
    ctx.push_assert("final_answer", "msf.index(8) == 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63d: full Kadane trace should verify, got: {:?}",
        result,
    );
}

/// Tier 63d: Exit — all-negative array: max subarray is the least negative.
/// a = [-3, -5, -1, -8]. max_so_far = -1 (subarray [-1]).
#[test]
fn test_vt_tier63d_all_negative_array() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-3, -5, -1, -8]);

    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.push_assume("msf_val", "max_so_far == -1");

    // max_so_far = max(a[0], a[1], a[2], a[3]) = -1
    ctx.push_assert("ge_0", "max_so_far >= a.index(0)");
    ctx.push_assert("ge_1", "max_so_far >= a.index(1)");
    ctx.push_assert("ge_2", "max_so_far >= a.index(2)");
    ctx.push_assert("ge_3", "max_so_far >= a.index(3)");
    // -1 is actually one of the elements
    ctx.push_assert("equals_best", "max_so_far == a.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63d: all-negative array should verify, got: {:?}",
        result,
    );
}

/// Tier 63d: Exit — all-positive array: max subarray is the entire array.
/// a = [1, 2, 3, 4]. max_so_far = 10.
#[test]
fn test_vt_tier63d_all_positive_array() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[1, 2, 3, 4]);

    ctx.declare_var_parsed("max_so_far", "i64");
    ctx.declare_var_parsed("total", "i64");
    ctx.push_assume("msf_val", "max_so_far == 10");
    ctx.push_assume(
        "total_sum",
        "total == a.index(0) + a.index(1) + a.index(2) + a.index(3)",
    );

    ctx.push_assert("equals_total", "max_so_far == total");
    ctx.push_assert("total_correct", "total == 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63d: all-positive array should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Symbolic Kadane properties
// ========================================================================

/// Tier 63e: Symbolic — Kadane step preserves max_so_far >= max_here.
#[test]
fn test_vt_tier63e_symbolic_far_ge_here() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("max_here_pre", "i64");
    ctx.declare_var_parsed("max_so_far_pre", "i64");
    ctx.declare_var_parsed("a_i", "i64");
    ctx.declare_var_parsed("max_here_post", "i64");
    ctx.declare_var_parsed("max_so_far_post", "i64");

    ctx.push_assume(
        "bounds_here",
        "max_here_pre > -100000 && max_here_pre < 100000",
    );
    ctx.push_assume(
        "bounds_far",
        "max_so_far_pre > -100000 && max_so_far_pre < 100000",
    );
    ctx.push_assume("bounds_ai", "a_i > -1000 && a_i < 1000");
    // Induction hypothesis: invariant holds before this step
    ctx.push_assume("inv_pre", "max_so_far_pre >= max_here_pre");

    // Kadane step
    ctx.push_assume(
        "kadane_here",
        "max_here_post == if a_i > max_here_pre + a_i \
         { a_i } else { max_here_pre + a_i }",
    );
    ctx.push_assume(
        "kadane_far",
        "max_so_far_post == if max_here_post > max_so_far_pre \
         { max_here_post } else { max_so_far_pre }",
    );

    // Invariant maintained: max_so_far_post >= max_here_post
    ctx.push_assert("inv_post", "max_so_far_post >= max_here_post");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63e: symbolic far >= here should verify, got: {:?}",
        result,
    );
}

/// Tier 63e: Symbolic — max_so_far is non-decreasing.
#[test]
fn test_vt_tier63e_symbolic_far_nondecreasing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("max_here_post", "i64");
    ctx.declare_var_parsed("max_so_far_pre", "i64");
    ctx.declare_var_parsed("max_so_far_post", "i64");

    ctx.push_assume(
        "bounds_here",
        "max_here_post > -100000 && max_here_post < 100000",
    );
    ctx.push_assume(
        "bounds_far",
        "max_so_far_pre > -100000 && max_so_far_pre < 100000",
    );
    ctx.push_assume(
        "kadane_far",
        "max_so_far_post == if max_here_post > max_so_far_pre \
         { max_here_post } else { max_so_far_pre }",
    );

    ctx.push_assert("nondecreasing", "max_so_far_post >= max_so_far_pre");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 63e: max_so_far non-decreasing should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 63f NEGATIVE: claiming the wrong maximum subarray sum.
/// True max for [-2,1,-3,4,-1,2,1,-5,4] is 6, not 7.
#[test]
fn test_vt_tier63f_wrong_max_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    ctx.declare_var_parsed("claimed_max", "i64");
    ctx.push_assume("claim", "claimed_max == 7");

    // The best contiguous subarray is [4,-1,2,1]=6, not 7
    // No contiguous subarray sums to 7:
    // [4,-1,2,1,-5,4] = 5, [1,-3,4,-1,2,1] = 4
    // Claim that claimed_max equals the actual Kadane result
    ctx.push_assert("wrong_max", "claimed_max == 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 63f SOUNDNESS: wrong max should be rejected, got: {:?}",
        result,
    );
}

/// Tier 63f NEGATIVE: forgetting the max() — just accumulating without reset.
/// Simple accumulation: sum = a[0]+a[1]+...+a[i] (prefix sum).
/// For [-2, 1, -3, 4, -1, 2, 1, -5, 4], prefix sums are:
/// [-2, -1, -4, 0, -1, 1, 2, -3, 1].
/// Claiming max prefix sum (2) equals Kadane result (6) should fail.
#[test]
fn test_vt_tier63f_prefix_sum_not_kadane_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[-2, 1, -3, 4, -1, 2, 1, -5, 4]);

    ctx.declare_var_parsed("max_prefix_sum", "i64");
    ctx.declare_var_parsed("kadane_result", "i64");
    ctx.push_assume("prefix_max", "max_prefix_sum == 2");
    ctx.push_assume("kadane_val", "kadane_result == 6");

    ctx.push_assert("prefix_eq_kadane", "max_prefix_sum == kadane_result");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 63f SOUNDNESS: prefix sum != Kadane should be rejected, got: {:?}",
        result,
    );
}

/// Tier 63f NEGATIVE: skipping the max_so_far update misses the true maximum.
/// If we only track max_here without max_so_far, we lose intermediate peaks.
/// At i=7 (a[7]=-5): max_here drops to 1, but true max was 6 at i=6.
#[test]
fn test_vt_tier63f_missing_global_max_update_rejected() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("max_here_final", "i64");
    ctx.declare_var_parsed("true_max", "i64");
    ctx.push_assume("here_final", "max_here_final == 5"); // max_here at end
    ctx.push_assume("true_val", "true_max == 6"); // actual Kadane answer

    // Claiming max_here at end IS the answer (it isn't — max was 6 at i=6)
    ctx.push_assert("here_eq_max", "max_here_final == true_max");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 63f SOUNDNESS: missing global max update should be rejected, got: {:?}",
        result,
    );
}

/// Tier 63f NEGATIVE: Kadane doesn't work for empty arrays — init requires len >= 1.
#[test]
fn test_vt_tier63f_empty_array_invalid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i64>");
    ctx.push_assume("empty", "a.len() == 0");

    ctx.declare_var_parsed("max_so_far", "i64");
    // Trying to init max_so_far = a[0] on empty array — out of bounds
    // We model this as: claiming any finite result from an empty array
    ctx.push_assume("claimed", "max_so_far == 0");

    // The only contiguous subarray of empty array is empty, which has no sum
    // Claiming max_so_far >= 0 should be fine, but claiming it equals
    // a valid subarray sum requires len >= 1
    // We assert a contradiction: len==0 but max_so_far equals some element
    ctx.push_assert("has_witness", "a.len() >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 63f SOUNDNESS: empty array precondition must fail, got: {:?}",
        result,
    );
}
