// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 71 — Largest Rectangle in Histogram VCs.
//!
//! The classic monotone-stack algorithm scans bar heights left to right.
//! While the next bar is lower than the current stack top, the algorithm pops
//! the taller bar, closes its maximal span, and updates the best area.
//!
//! Core proof obligations:
//!   1. Pushes preserve increasing indices and strictly increasing heights.
//!   2. A lower incoming bar forces one or more pops.
//!   3. The pop width is determined by the new left boundary and current index.
//!   4. Final stack flush uses the array length as the right boundary.
//!   5. Negatives: wrong left boundaries, skipped pops, or wrong heights are unsound.
//!
//! We use the standard example histogram `[2, 1, 5, 6, 2, 3]`, whose maximum
//! rectangle area is `10`.
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

fn assume_histogram_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "heights", &[2, 1, 5, 6, 2, 3]);
}

// ========================================================================
// GROUP A: Monotone stack push discipline
// ========================================================================

/// Tier 71a: the scan seeds the stack with the first bar.
#[test]
fn test_vt_tier71a_seed_stack_with_first_bar() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("stack_len", "u64");
    ctx.declare_var_parsed("top", "u64");

    ctx.push_assume("stack_len_1", "stack_len == 1");
    ctx.push_assume("top_0", "top == 0");

    ctx.push_assert("top_in_bounds", "top < heights.len()");
    ctx.push_assert("first_height", "heights.index(top) == 2");
    ctx.push_assert("nonempty_stack", "stack_len >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71a: seeding the stack should verify, got: {:?}",
        result,
    );
}

/// Tier 71a: pushing a higher bar preserves the stack's increasing-height invariant.
#[test]
fn test_vt_tier71a_push_rising_bar_preserves_monotonicity() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("lower", "u64");
    ctx.declare_var_parsed("top", "u64");
    ctx.declare_var_parsed("current", "u64");

    ctx.push_assume("lower_1", "lower == 1");
    ctx.push_assume("top_2", "top == 2");
    ctx.push_assume("current_3", "current == 3");

    ctx.push_assert("index_order_0", "lower < top");
    ctx.push_assert("index_order_1", "top < current");
    ctx.push_assert(
        "height_order_0",
        "heights.index(lower) < heights.index(top)",
    );
    ctx.push_assert(
        "height_order_1",
        "heights.index(top) < heights.index(current)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71a: pushing a rising bar should preserve monotonicity, got: {:?}",
        result,
    );
}

/// Tier 71a: the lower bar at index 4 forces pops of the taller suffix.
#[test]
fn test_vt_tier71a_lower_bar_forces_pop_condition() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("lower", "u64");
    ctx.declare_var_parsed("top", "u64");
    ctx.declare_var_parsed("current", "u64");

    ctx.push_assume("lower_2", "lower == 2");
    ctx.push_assume("top_3", "top == 3");
    ctx.push_assume("current_4", "current == 4");

    ctx.push_assert(
        "first_pop_required",
        "heights.index(top) > heights.index(current)",
    );
    ctx.push_assert(
        "second_pop_also_required",
        "heights.index(lower) > heights.index(current)",
    );
    ctx.push_assert("taller_suffix", "heights.index(top) > heights.index(lower)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71a: lower incoming bar should force pops, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Pop width and area calculations
// ========================================================================

/// Tier 71b: popping height 6 at index 3 yields width 1 and area 6.
#[test]
fn test_vt_tier71b_first_pop_width_and_area() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("left", "u64");
    ctx.declare_var_parsed("popped", "u64");
    ctx.declare_var_parsed("current", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("area", "u64");

    ctx.push_assume("left_2", "left == 2");
    ctx.push_assume("popped_3", "popped == 3");
    ctx.push_assume("current_4", "current == 4");
    ctx.push_assume("width_1", "width == 1");
    ctx.push_assume("area_6", "area == 6");

    ctx.push_assert("width_relation", "left + width + 1 == current");
    ctx.push_assert("height_is_6", "heights.index(popped) == 6");
    ctx.push_assert("unit_width_area", "area == heights.index(popped)");
    ctx.push_assert(
        "current_is_lower",
        "heights.index(current) < heights.index(popped)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71b: first pop width/area should verify, got: {:?}",
        result,
    );
}

/// Tier 71b: the second pop widens to the previous smaller bar and yields area 10.
#[test]
fn test_vt_tier71b_second_pop_expands_to_previous_smaller_bar() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("left", "u64");
    ctx.declare_var_parsed("popped", "u64");
    ctx.declare_var_parsed("current", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("area", "u64");

    ctx.push_assume("left_1", "left == 1");
    ctx.push_assume("popped_2", "popped == 2");
    ctx.push_assume("current_4", "current == 4");
    ctx.push_assume("width_2", "width == 2");
    ctx.push_assume("area_10", "area == 10");

    ctx.push_assert("width_relation", "left + width + 1 == current");
    ctx.push_assert(
        "left_is_smaller",
        "heights.index(left) < heights.index(popped)",
    );
    ctx.push_assert(
        "current_is_smaller",
        "heights.index(current) < heights.index(popped)",
    );
    ctx.push_assert(
        "double_height_area",
        "area == heights.index(popped) + heights.index(popped)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71b: second pop should recover the maximal area, got: {:?}",
        result,
    );
}

/// Tier 71b: consecutive pops strictly widen the span and improve the best area.
#[test]
fn test_vt_tier71b_consecutive_pops_increase_width_and_best_area() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("first_width", "u64");
    ctx.declare_var_parsed("second_width", "u64");
    ctx.declare_var_parsed("first_area", "u64");
    ctx.declare_var_parsed("second_area", "u64");

    ctx.push_assume("first_width_1", "first_width == 1");
    ctx.push_assume("second_width_2", "second_width == 2");
    ctx.push_assume("first_area_6", "first_area == 6");
    ctx.push_assume("second_area_10", "second_area == 10");

    ctx.push_assert("width_grows", "second_width > first_width");
    ctx.push_assert("area_grows", "second_area > first_area");
    ctx.push_assert("first_height_is_6", "heights.index(3) == first_area");
    ctx.push_assert(
        "second_area_matches_double_height",
        "second_area == heights.index(2) + heights.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71b: consecutive pops should widen the span, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Final flush and global optimum
// ========================================================================

/// Tier 71c: flushing the trailing height 3 at index 5 uses the array length as the right boundary.
#[test]
fn test_vt_tier71c_final_flush_uses_array_length_boundary() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("left", "u64");
    ctx.declare_var_parsed("popped", "u64");
    ctx.declare_var_parsed("current", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("area", "u64");

    ctx.push_assume("left_4", "left == 4");
    ctx.push_assume("popped_5", "popped == 5");
    ctx.push_assume("current_len", "current == heights.len()");
    ctx.push_assume("width_1", "width == 1");
    ctx.push_assume("area_3", "area == 3");

    ctx.push_assert("flush_width_relation", "left + width + 1 == current");
    ctx.push_assert("flush_height", "area == heights.index(popped)");
    ctx.push_assert("uses_full_length", "current == 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71c: final flush should use the array length boundary, got: {:?}",
        result,
    );
}

/// Tier 71c: once the stack is empty, the remaining height 1 spans the full width 6.
#[test]
fn test_vt_tier71c_empty_stack_pop_uses_full_width() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("popped", "u64");
    ctx.declare_var_parsed("width", "u64");
    ctx.declare_var_parsed("area", "u64");

    ctx.push_assume("popped_1", "popped == 1");
    ctx.push_assume("width_len", "width == heights.len()");
    ctx.push_assume("area_6", "area == 6");

    ctx.push_assert("width_is_6", "width == 6");
    ctx.push_assert("height_is_1", "heights.index(popped) == 1");
    ctx.push_assert("full_width_matches_area", "area == width");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71c: empty-stack pop should use the full width, got: {:?}",
        result,
    );
}

/// Tier 71c: the classic example's candidate areas are all bounded by the best area 10.
#[test]
fn test_vt_tier71c_example_max_area_is_ten() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("area0", "u64");
    ctx.declare_var_parsed("area1", "u64");
    ctx.declare_var_parsed("area2", "u64");
    ctx.declare_var_parsed("area3", "u64");
    ctx.declare_var_parsed("area4", "u64");
    ctx.declare_var_parsed("area5", "u64");
    ctx.declare_var_parsed("best", "u64");

    ctx.push_assume("area0_2", "area0 == 2");
    ctx.push_assume("area1_6", "area1 == 6");
    ctx.push_assume("area2_10", "area2 == 10");
    ctx.push_assume("area3_6", "area3 == 6");
    ctx.push_assume("area4_8", "area4 == 8");
    ctx.push_assume("area5_3", "area5 == 3");
    ctx.push_assume("best_10", "best == 10");

    ctx.push_assert("area0_bounded", "area0 <= best");
    ctx.push_assert("area1_bounded", "area1 <= best");
    ctx.push_assert("area2_hits_best", "area2 == best");
    ctx.push_assert("area3_bounded", "area3 <= best");
    ctx.push_assert("area4_bounded", "area4 <= best");
    ctx.push_assert("area5_bounded", "area5 <= best");
    ctx.push_assert("best_beats_area4", "best > area4");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 71c: example best area should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 71d NEGATIVE: using the wrong left boundary overestimates the maximal area.
#[test]
fn test_vt_tier71d_wrong_left_boundary_overestimates_area() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("wrong_left", "u64");
    ctx.declare_var_parsed("current", "u64");
    ctx.declare_var_parsed("wrong_width", "u64");
    ctx.declare_var_parsed("wrong_area", "u64");

    ctx.push_assume("wrong_left_0", "wrong_left == 0");
    ctx.push_assume("current_4", "current == 4");
    ctx.push_assume("wrong_width_3", "wrong_width == 3");
    ctx.push_assume("wrong_area_15", "wrong_area == 15");

    ctx.push_assert(
        "wrong_span_relation",
        "wrong_left + wrong_width + 1 == current",
    );
    ctx.push_assert("bar_height_is_5", "heights.index(2) == 5");
    ctx.push_assert("claimed_optimal", "wrong_area <= 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 71d SOUNDNESS: wrong left boundary should be rejected, got: {:?}",
        result,
    );
}

/// Tier 71d NEGATIVE: keeping a taller bar on the stack when the next bar is smaller is unsound.
#[test]
fn test_vt_tier71d_skipping_required_pop_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("top", "u64");
    ctx.declare_var_parsed("current", "u64");

    ctx.push_assume("top_3", "top == 3");
    ctx.push_assume("current_4", "current == 4");

    ctx.push_assert(
        "claimed_monotone",
        "heights.index(top) <= heights.index(current)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 71d SOUNDNESS: skipping a required pop should be rejected, got: {:?}",
        result,
    );
}

/// Tier 71d NEGATIVE: using the current bar's height instead of the popped height loses the max rectangle.
#[test]
fn test_vt_tier71d_using_current_height_for_area_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_histogram_example(&mut ctx);
    ctx.declare_var_parsed("wrong_area", "u64");

    ctx.push_assume("wrong_area_def", "wrong_area == heights.index(4) * 2");
    ctx.push_assert("claimed_best", "wrong_area == 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 71d SOUNDNESS: using the current height for area should be rejected, got: {:?}",
        result,
    );
}
