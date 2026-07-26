// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 74 - Sliding Window Maximum / Monotonic Deque VCs.
//!
//! Sliding-window maximum is a classic competition problem: scan left-to-right,
//! maintain candidate indices in decreasing-value order, evict indices that
//! leave the window, and read the current maximum from the deque front.
//!
//! Core proof obligations:
//!   1. Candidate indices stay strictly increasing.
//!   2. Candidate values stay non-increasing from front to back.
//!   3. A larger incoming value removes the smaller suffix before push.
//!   4. When the front index leaves the window, it is evicted.
//!   5. The deque front equals the current window maximum.
//!   6. Negatives: keeping an expired front, allowing increasing deque values,
//!      or reading the tail as the maximum are unsound.
//!
//! Example sequence:
//!   values = [1, 3, 1, 2, 0, 5], window width = 3
//!
//! Concrete deque traces (indices):
//!   after 0: [0]
//!   after 1: [1]        (value 3 pops value 1)
//!   after 2: [1, 2]
//!   after 3: [1, 3]     (value 2 pops index 2)
//!   after 4: [3, 4]     (index 1 expired)
//!   after 5: [5]        (value 5 pops the whole suffix)
//!
//! Window maxima are [3, 3, 2, 5].
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

fn assume_window_maximum_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "values", &[1, 3, 1, 2, 0, 5]);
    assume_seq_u64(ctx, "deque_0", &[0]);
    assume_seq_u64(ctx, "deque_1", &[1]);
    assume_seq_u64(ctx, "deque_2", &[1, 2]);
    assume_seq_u64(ctx, "deque_3", &[1, 3]);
    assume_seq_u64(ctx, "deque_4", &[3, 4]);
    assume_seq_u64(ctx, "deque_5", &[5]);
    assume_seq_u64(ctx, "maxima", &[3, 3, 2, 5]);
}

// ========================================================================
// GROUP A: Seed and first pop
// ========================================================================

/// Tier 74a: the first element seeds the deque with one candidate index.
#[test]
fn test_vt_tier74a_first_element_seeds_deque() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert("deque_0_singleton", "deque_0.len() == 1");
    ctx.push_assert("deque_0_front", "deque_0.index(0) == 0");
    ctx.push_assert(
        "front_points_to_first_value",
        "values.index(deque_0.index(0)) == values.index(0)",
    );
    ctx.push_assert("window_fits_sequence", "maxima.len() + 2 == values.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74a: first element should seed the deque, got: {:?}",
        result,
    );
}

/// Tier 74a: the larger second element pops the first candidate and becomes the new front.
#[test]
fn test_vt_tier74a_larger_second_value_replaces_first_candidate() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "second_value_is_larger",
        "values.index(1) > values.index(deque_0.index(0))",
    );
    ctx.push_assert("deque_1_singleton", "deque_1.len() == 1");
    ctx.push_assert("deque_1_front", "deque_1.index(0) == 1");
    ctx.push_assert(
        "new_front_matches_window_max",
        "values.index(deque_1.index(0)) == maxima.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74a: larger second value should replace the first candidate, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Monotonic deque maintenance
// ========================================================================

/// Tier 74b: the third value appends behind the current maximum without violating monotonicity.
#[test]
fn test_vt_tier74b_third_value_appends_behind_front() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert("deque_2_has_two_candidates", "deque_2.len() == 2");
    ctx.push_assert("indices_increase", "deque_2.index(0) < deque_2.index(1)");
    ctx.push_assert(
        "front_value_dominates_tail",
        "values.index(deque_2.index(0)) >= values.index(deque_2.index(1))",
    );
    ctx.push_assert(
        "front_preserved_from_previous_step",
        "deque_2.index(0) == deque_1.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74b: third value should append behind the front, got: {:?}",
        result,
    );
}

/// Tier 74b: the value 2 at index 3 pops the smaller suffix index 2 before it is pushed.
#[test]
fn test_vt_tier74b_larger_incoming_value_pops_smaller_suffix() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "incoming_exceeds_suffix_tail",
        "values.index(3) > values.index(deque_2.index(1))",
    );
    ctx.push_assert("deque_3_has_two_candidates", "deque_3.len() == 2");
    ctx.push_assert("front_survives_pop", "deque_3.index(0) == deque_2.index(0)");
    ctx.push_assert("new_tail_is_index_3", "deque_3.index(1) == 3");
    ctx.push_assert(
        "new_tail_keeps_value_order",
        "values.index(deque_3.index(0)) >= values.index(deque_3.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74b: incoming larger value should pop the smaller suffix, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Eviction and window maxima
// ========================================================================

/// Tier 74c: the deque front matches the maxima of the first two windows.
#[test]
fn test_vt_tier74c_front_matches_first_two_window_maxima() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "first_window_max_from_front",
        "maxima.index(0) == values.index(deque_2.index(0))",
    );
    ctx.push_assert(
        "second_window_max_from_front",
        "maxima.index(1) == values.index(deque_3.index(0))",
    );
    ctx.push_assert(
        "first_two_maxima_equal",
        "maxima.index(0) == maxima.index(1)",
    );
    ctx.push_assert(
        "front_value_exceeds_second_candidate",
        "values.index(deque_3.index(0)) > values.index(deque_3.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74c: deque front should match the first two window maxima, got: {:?}",
        result,
    );
}

/// Tier 74c: once index 1 leaves the window, the deque evicts it and the front moves to index 3.
#[test]
fn test_vt_tier74c_expired_front_is_evicted() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);
    ctx.declare_var_parsed("window_start", "u64");
    ctx.push_assume("window_start_2", "window_start == 2");

    ctx.push_assert("old_front_expired", "deque_3.index(0) < window_start");
    ctx.push_assert("new_front_is_index_3", "deque_4.index(0) == 3");
    ctx.push_assert("new_tail_is_index_4", "deque_4.index(1) == 4");
    ctx.push_assert(
        "front_still_dominates_tail",
        "values.index(deque_4.index(0)) >= values.index(deque_4.index(1))",
    );
    ctx.push_assert(
        "third_window_max_from_new_front",
        "maxima.index(2) == values.index(deque_4.index(0))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74c: expired front should be evicted when the window advances, got: {:?}",
        result,
    );
}

/// Tier 74c: the final value 5 clears the deque suffix and becomes the sole candidate and max.
#[test]
fn test_vt_tier74c_final_large_value_clears_suffix() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "final_value_beats_front",
        "values.index(5) > values.index(deque_4.index(0))",
    );
    ctx.push_assert(
        "final_value_beats_tail",
        "values.index(5) > values.index(deque_4.index(1))",
    );
    ctx.push_assert("deque_5_singleton", "deque_5.len() == 1");
    ctx.push_assert("deque_5_front_is_5", "deque_5.index(0) == 5");
    ctx.push_assert(
        "last_window_max_from_singleton_front",
        "maxima.index(3) == values.index(deque_5.index(0))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74c: final large value should clear the suffix and become the max, got: {:?}",
        result,
    );
}

/// Tier 74c: the full trace yields the expected four window maxima.
#[test]
fn test_vt_tier74c_full_trace_matches_window_maxima() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert("maxima_len", "maxima.len() == 4");
    ctx.push_assert(
        "first_window_front",
        "maxima.index(0) == values.index(deque_2.index(0))",
    );
    ctx.push_assert(
        "second_window_front",
        "maxima.index(1) == values.index(deque_3.index(0))",
    );
    ctx.push_assert(
        "third_window_front",
        "maxima.index(2) == values.index(deque_4.index(0))",
    );
    ctx.push_assert(
        "fourth_window_front",
        "maxima.index(3) == values.index(deque_5.index(0))",
    );
    ctx.push_assert(
        "late_max_exceeds_middle",
        "maxima.index(3) > maxima.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 74c: full sliding-window maximum trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 74d NEGATIVE: keeping the expired front from index 1 after the window starts at 2 is unsound.
#[test]
fn test_vt_tier74d_keeping_expired_front_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "stale_front_retained",
        "deque_4.index(0) == deque_3.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 74d SOUNDNESS: keeping the expired front should be rejected, got: {:?}",
        result,
    );
}

/// Tier 74d NEGATIVE: deque values must not increase toward the back.
#[test]
fn test_vt_tier74d_increasing_values_toward_back_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "wrong_value_order",
        "values.index(deque_3.index(0)) < values.index(deque_3.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 74d SOUNDNESS: increasing values toward the back should be rejected, got: {:?}",
        result,
    );
}

/// Tier 74d NEGATIVE: the tail candidate cannot be reported as the third window maximum.
#[test]
fn test_vt_tier74d_tail_cannot_be_reported_as_window_maximum() {
    let mut ctx = VerificationContext::new();
    assume_window_maximum_example(&mut ctx);

    ctx.push_assert(
        "tail_as_third_window_max",
        "maxima.index(2) == values.index(deque_4.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 74d SOUNDNESS: deque tail should not be the third window maximum, got: {:?}",
        result,
    );
}
