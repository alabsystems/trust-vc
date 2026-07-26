// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 37 — Binary Search VCs.
//!
//! Binary search is a fundamental competition pattern. VerifyThis-style
//! problems frequently require proving correctness of search, partition-point,
//! or lower/upper-bound queries over sorted arrays. The key proof obligations:
//!
//!   1. **Invariant preservation**: the target stays within [lo, hi) after
//!      each compare-and-narrow step.
//!   2. **Termination**: hi - lo decreases every iteration.
//!   3. **Post-condition**: s[mid] == target when found.
//!   4. **Soundness negatives**: off-by-one updates and unsorted inputs break
//!      the invariant.
//!
//! We model a sorted `Seq<i64>` (signed to exercise negative elements) and
//! trace concrete + symbolic binary-search steps. The step tests leave
//! target_idx symbolic, forcing the solver to determine the target position
//! from array values rather than echoing an assumed index.
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

/// Assume the sorted 8-element array [1, 3, 5, 7, 9, 11, 13, 15].
fn assume_sorted_8(ctx: &mut VerificationContext) {
    assume_seq_i64(ctx, "s", &[1, 3, 5, 7, 9, 11, 13, 15]);
}

// ========================================================================
// GROUP A: Step-preservation invariants
//
// Core binary-search reasoning: given a sorted array and an element known
// to lie in [lo, hi), comparing s[mid] with the target narrows the range
// while preserving the invariant.
//
// target_idx is left SYMBOLIC — the solver must determine which index
// holds the target value from the concrete array, not from a given index.
// ========================================================================

/// Tier 37a: Step low — s[mid] < target implies target in [mid+1, hi).
///
/// Sorted 8-element array [1, 3, 5, 7, 9, 11, 13, 15], target = 11.
/// lo=0, hi=8, mid=4, s[4]=9 < 11.
/// Solver must determine target_idx == 5 from array values, then verify
/// 5 >= mid+1 = 5. No concrete target_idx assumed.
#[test]
fn test_vt_tier37a_step_low_preserves_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("target_idx", "u64");

    assume_sorted_8(&mut ctx);

    ctx.push_assume("tgt", "target == 11");
    // Target exists in array — index NOT given, solver must derive it
    ctx.push_assume("ti_bound", "target_idx < 8");
    ctx.push_assume("at_target", "s.index(target_idx) == target");

    // Pre-state: target_idx in [lo, hi)
    ctx.push_assume("lo_val", "lo == 0");
    ctx.push_assume("hi_val", "hi == 8");
    ctx.push_assume("inv_pre", "target_idx >= lo && target_idx < hi");

    // Step: mid = 4, s[mid] < target => lo' = mid + 1 = 5
    ctx.push_assume("mid_val", "mid == 4");
    ctx.push_assume("compare", "s.index(mid) < target");

    // Post-state invariant: target_idx in [mid+1, hi)
    // Solver must derive target_idx from array values to verify
    ctx.push_assert("inv_post_lo", "target_idx >= mid + 1");
    ctx.push_assert("inv_post_hi", "target_idx < hi");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37a: step-low should preserve invariant, got: {:?}",
        result,
    );
}

/// Tier 37b: Step high — s[mid] > target implies target in [lo, mid).
///
/// Continuing from step 1: lo=5, hi=8, mid=6, s[6]=13 > 11.
/// Solver must determine target_idx from array values and verify < mid.
#[test]
fn test_vt_tier37b_step_high_preserves_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("target_idx", "u64");

    assume_sorted_8(&mut ctx);

    ctx.push_assume("tgt", "target == 11");
    ctx.push_assume("ti_bound", "target_idx < 8");
    ctx.push_assume("at_target", "s.index(target_idx) == target");

    // Pre-state: target_idx in [5, 8)
    ctx.push_assume("lo_val", "lo == 5");
    ctx.push_assume("hi_val", "hi == 8");
    ctx.push_assume("inv_pre", "target_idx >= lo && target_idx < hi");

    // Step: mid = 6, s[mid] > target => hi' = mid = 6
    ctx.push_assume("mid_val", "mid == 6");
    ctx.push_assume("compare", "s.index(mid) > target");

    // Post-state invariant: target_idx in [lo, mid)
    ctx.push_assert("inv_post_lo", "target_idx >= lo");
    ctx.push_assert("inv_post_hi", "target_idx < mid");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37b: step-high should preserve invariant, got: {:?}",
        result,
    );
}

/// Tier 37c: Found — s[mid] == target implies correct result.
///
/// Final step: lo=5, hi=6, mid=5, s[5]=11 == target. Done.
#[test]
fn test_vt_tier37c_found_implies_correct_result() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("mid", "u64");

    assume_sorted_8(&mut ctx);

    ctx.push_assume("tgt", "target == 11");
    ctx.push_assume("mid_val", "mid == 5");
    ctx.push_assume("found", "s.index(mid) == target");

    // Result correctness: value and index match
    ctx.push_assert("result_correct", "s.index(mid) == 11");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37c: found case should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Full trace and termination
// ========================================================================

/// Tier 37d: Full 3-step trace — searching for 11 in [1,3,5,7,9,11,13,15].
///
/// Step transitions defined via expressions from prior state variables.
/// Cross-step assertions verify progress and convergence.
#[test]
fn test_vt_tier37d_full_trace_three_steps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("lo0", "u64");
    ctx.declare_var_parsed("hi0", "u64");
    ctx.declare_var_parsed("mid0", "u64");
    ctx.declare_var_parsed("lo1", "u64");
    ctx.declare_var_parsed("hi1", "u64");
    ctx.declare_var_parsed("mid1", "u64");
    ctx.declare_var_parsed("lo2", "u64");
    ctx.declare_var_parsed("hi2", "u64");
    ctx.declare_var_parsed("mid2", "u64");

    assume_sorted_8(&mut ctx);
    ctx.push_assume("tgt", "target == 11");

    // Step 1: lo=0, hi=8, mid=4, s[4]=9 < 11 → lo-step
    ctx.push_assume("init_lo", "lo0 == 0");
    ctx.push_assume("init_hi", "hi0 == 8");
    ctx.push_assume("mid0_val", "mid0 == 4");
    ctx.push_assume("cmp0", "s.index(mid0) < target");
    ctx.push_assume("step1_lo", "lo1 == mid0 + 1");
    ctx.push_assume("step1_hi", "hi1 == hi0");

    // Step 2: lo=5, hi=8, mid=6, s[6]=13 > 11 → hi-step
    ctx.push_assume("mid1_val", "mid1 == 6");
    ctx.push_assume("cmp1", "s.index(mid1) > target");
    ctx.push_assume("step2_lo", "lo2 == lo1");
    ctx.push_assume("step2_hi", "hi2 == mid1");

    // Step 3: lo=5, hi=6, mid=5, found
    ctx.push_assume("mid2_val", "mid2 == 5");
    ctx.push_assume("cmp2", "s.index(mid2) == target");

    // Cross-step progress: search range shrinks each step
    ctx.push_assert("progress_step1", "hi1 - lo1 < hi0 - lo0");
    ctx.push_assert("progress_step2", "hi2 - lo2 < hi1 - lo1");
    // Final convergence: singleton range
    ctx.push_assert("range_singleton", "hi2 == lo2 + 1");
    // Found value matches target (derived through expression chain)
    ctx.push_assert("found_val", "s.index(mid2) == 11");
    // Search narrowed from both sides
    ctx.push_assert("lo_advanced", "lo2 > lo0");
    ctx.push_assert("hi_retreated", "hi2 < hi0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37d: full 3-step trace should verify, got: {:?}",
        result,
    );
}

/// Tier 37e: Termination — interval strictly shrinks each step.
///
/// Symbolic: given lo < hi, mid in [lo, hi), the new interval is strictly
/// smaller whether we update lo = mid+1 or hi = mid.
#[test]
fn test_vt_tier37e_interval_shrinks_each_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("width_lo", "u64");
    ctx.declare_var_parsed("width_hi", "u64");

    // lo < hi (non-empty interval)
    ctx.push_assume("nonempty", "lo < hi");
    ctx.push_assume("bounded", "hi <= 1000");
    // mid = (lo + hi) / 2, which is in [lo, hi)
    ctx.push_assume("mid_bounds", "mid >= lo && mid < hi");

    ctx.push_assume("width_def", "width == hi - lo");

    // Case: lo' = mid + 1 (step-low)
    ctx.push_assume("width_lo_def", "width_lo == hi - (mid + 1)");
    // Case: hi' = mid (step-high)
    ctx.push_assume("width_hi_def", "width_hi == mid - lo");

    // Both branches strictly decrease the interval
    ctx.push_assert("shrink_lo", "width_lo < width");
    ctx.push_assert("shrink_hi", "width_hi < width");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37e: interval should shrink each step, got: {:?}",
        result,
    );
}

/// Tier 37f: Symbolic step-low — sortedness implies invariant preservation.
///
/// 4-element sorted array (symbolic but constrained by pairwise ordering).
/// If s[mid] < target and target == s[target_idx], then target_idx > mid.
/// This is the general argument, not a concrete trace.
#[test]
fn test_vt_tier37f_symbolic_sorted_step_low() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("target_idx", "u64");

    ctx.push_assume("len", "s.len() == 4");
    // Pairwise sortedness: s[0] <= s[1] <= s[2] <= s[3]
    ctx.push_assume("sorted01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted12", "s.index(1) <= s.index(2)");
    ctx.push_assume("sorted23", "s.index(2) <= s.index(3)");

    // Target exists in the array
    ctx.push_assume("ti_bound", "target_idx < 4");
    ctx.push_assume("at_target", "s.index(target_idx) == target");

    // Mid is a valid index with s[mid] < target
    ctx.push_assume("mid_bound", "mid < 4");
    ctx.push_assume("compare", "s.index(mid) < target");

    // Claim: target_idx > mid (i.e., target is in the upper half)
    ctx.push_assert("target_above_mid", "target_idx > mid");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 37f: symbolic sorted step-low should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 37g: Off-by-one — using lo' = mid instead of mid+1 can lose the target.
///
/// With the off-by-one, the interval can fail to shrink (mid == lo when
/// hi == lo + 2), violating termination.
#[test]
fn test_vt_tier37g_off_by_one_stall_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("width_new", "u64");

    ctx.push_assume("nonempty", "lo < hi");
    ctx.push_assume("bounded", "hi <= 1000");
    ctx.push_assume("mid_bounds", "mid >= lo && mid < hi");
    ctx.push_assume("width_def", "width == hi - lo");

    // WRONG: lo' = mid (not mid + 1)
    ctx.push_assume("width_new_def", "width_new == hi - mid");

    // Claim: width always shrinks — FALSE for off-by-one (lo=0, hi=2, mid=0)
    ctx.push_assert("always_shrinks", "width_new < width");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 37g SOUNDNESS: off-by-one should produce a counterexample, got: {:?}",
        result,
    );
}

/// Tier 37h: Unsorted array — step-low reasoning breaks without sortedness.
///
/// Without sortedness, s[mid] < target does NOT imply target_idx > mid.
/// Counterexample: s = [5, 1, 3, 7], target = 5, target_idx = 0, mid = 2,
/// s[2] = 3 < 5 but target_idx = 0 < mid = 2.
#[test]
fn test_vt_tier37h_unsorted_breaks_step_reasoning_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("target", "i64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("target_idx", "u64");

    ctx.push_assume("len", "s.len() == 4");
    // NO sortedness assumption
    ctx.push_assume("ti_bound", "target_idx < 4");
    ctx.push_assume("at_target", "s.index(target_idx) == target");
    ctx.push_assume("mid_bound", "mid < 4");
    ctx.push_assume("compare", "s.index(mid) < target");

    // Without sortedness, this should NOT always hold
    ctx.push_assert("target_above_mid", "target_idx > mid");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 37h SOUNDNESS: unsorted array should produce a counterexample, got: {:?}",
        result,
    );
}
