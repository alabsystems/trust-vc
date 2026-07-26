// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 79 - Dynamic Array Resize / Amortized Push VCs.
//!
//! Dynamic arrays back many VerifyThis-style data structures: worklists,
//! buffers, hash-table buckets, and growable frontiers. The core proof shape
//! is the grow-on-full append:
//!   1. appending with spare capacity preserves the existing live prefix
//!   2. appending to a full buffer doubles capacity before writing the new tail
//!   3. the resize copy loop extends the copied prefix one slot at a time
//!   4. the logical post-state is the old live prefix plus the fresh element
//!   5. the dense/full push cases stay constant-amortized under
//!      `potential = 2 * len - cap`
//!   6. negatives: failing to grow, dropping a copied element, or charging the
//!      full resize cost after potential accounting are unsound
//!
//! Concrete resize example:
//!   old live = [2, 5, 7, 9], len = 4, cap = 4
//!   push 11
//!   new live = [2, 5, 7, 9, 11], len = 5, cap = 8
//!
//! 10 tests: 7 positive (append, copy loop, logical post-state, amortized cost) + 3 negatives.
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

fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", exprs.len()),
    );
    for (index, expr) in exprs.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {expr}"),
        );
    }
}

fn assume_resize_copy_step_example(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("copied_old", "u64");
    ctx.declare_var_parsed("copied_new", "u64");
    ctx.declare_var_parsed("cap_new", "u64");

    assume_seq_i64(ctx, "buf_old", &[2, 5, 7, 9]);
    assume_seq_exprs(
        ctx,
        "partial_before",
        &[
            "buf_old.index(0)",
            "buf_old.index(1)",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
        ],
    );
    assume_seq_exprs(
        ctx,
        "partial_after",
        &[
            "partial_before.index(0)",
            "partial_before.index(1)",
            "buf_old.index(2)",
            "0",
            "0",
            "0",
            "0",
            "0",
        ],
    );

    ctx.push_assume("copied_old_val", "copied_old == 2");
    ctx.push_assume("copied_new_val", "copied_new == 3");
    ctx.push_assume("cap_new_val", "cap_new == 8");
}

// ========================================================================
// GROUP A: Append step correctness
// ========================================================================

/// Tier 79a: append within spare capacity keeps the old live prefix intact.
#[test]
fn test_vt_tier79a_append_without_resize_preserves_live_prefix() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fresh", "i64");
    ctx.declare_var_parsed("len_old", "u64");
    ctx.declare_var_parsed("len_new", "u64");
    ctx.declare_var_parsed("cap", "u64");

    assume_seq_i64(&mut ctx, "buf_old", &[4, 9, 12, 0]);
    assume_seq_exprs(
        &mut ctx,
        "buf_new",
        &[
            "buf_old.index(0)",
            "buf_old.index(1)",
            "buf_old.index(2)",
            "fresh",
        ],
    );

    ctx.push_assume("fresh_val", "fresh == 15");
    ctx.push_assume("len_old_val", "len_old == 3");
    ctx.push_assume("len_new_val", "len_new == 4");
    ctx.push_assume("cap_val", "cap == 4");

    ctx.push_assert("old_not_full", "len_old < cap");
    ctx.push_assert("len_increments", "len_new == len_old + 1");
    ctx.push_assert("copied_0", "buf_new.index(0) == buf_old.index(0)");
    ctx.push_assert("copied_1", "buf_new.index(1) == buf_old.index(1)");
    ctx.push_assert("copied_2", "buf_new.index(2) == buf_old.index(2)");
    ctx.push_assert("fresh_tail", "buf_new.index(3) == fresh");
    ctx.push_assert("new_len_fits_cap", "len_new <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79a: append without resize should verify, got: {:?}",
        result,
    );
}

/// Tier 79a: appending to a full buffer doubles capacity before writing.
#[test]
fn test_vt_tier79a_full_append_doubles_capacity_before_write() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fresh", "i64");
    ctx.declare_var_parsed("len_old", "u64");
    ctx.declare_var_parsed("len_new", "u64");
    ctx.declare_var_parsed("cap_old", "u64");
    ctx.declare_var_parsed("cap_new", "u64");

    assume_seq_i64(&mut ctx, "buf_old", &[2, 5, 7, 9]);
    assume_seq_exprs(
        &mut ctx,
        "buf_new",
        &[
            "buf_old.index(0)",
            "buf_old.index(1)",
            "buf_old.index(2)",
            "buf_old.index(3)",
            "fresh",
            "0",
            "0",
            "0",
        ],
    );

    ctx.push_assume("fresh_val", "fresh == 11");
    ctx.push_assume("len_old_val", "len_old == 4");
    ctx.push_assume("len_new_val", "len_new == 5");
    ctx.push_assume("cap_old_val", "cap_old == 4");
    ctx.push_assume("cap_new_val", "cap_new == 8");

    ctx.push_assert("old_is_full", "len_old == cap_old");
    ctx.push_assert("cap_doubles", "cap_new == cap_old + cap_old");
    ctx.push_assert("len_increments", "len_new == len_old + 1");
    ctx.push_assert(
        "copied_last_live_slot",
        "buf_new.index(3) == buf_old.index(3)",
    );
    ctx.push_assert("fresh_tail", "buf_new.index(4) == fresh");
    ctx.push_assert("new_len_fits_new_cap", "len_new <= cap_new");
    ctx.push_assert("spare_capacity_restored", "len_new < cap_new");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79a: full append should double capacity and verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Resize copy-loop and logical post-state
// ========================================================================

/// Tier 79b: one copy-loop step extends the copied prefix by exactly one slot.
#[test]
fn test_vt_tier79b_copy_step_extends_copied_prefix() {
    let mut ctx = VerificationContext::new();
    assume_resize_copy_step_example(&mut ctx);

    ctx.push_assert("copy_progresses", "copied_new == copied_old + 1");
    ctx.push_assert(
        "previous_prefix_kept_0",
        "partial_after.index(0) == partial_before.index(0)",
    );
    ctx.push_assert(
        "previous_prefix_kept_1",
        "partial_after.index(1) == partial_before.index(1)",
    );
    ctx.push_assert(
        "new_slot_copies_old_value",
        "partial_after.index(2) == buf_old.index(2)",
    );
    ctx.push_assert("copied_prefix_in_bounds", "copied_new <= cap_new");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79b: copy-step prefix extension should verify, got: {:?}",
        result,
    );
}

/// Tier 79b: after resize, the logical live prefix is the old contents plus the fresh tail.
#[test]
fn test_vt_tier79b_post_resize_live_prefix_matches_old_plus_fresh() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fresh", "i64");

    assume_seq_i64(&mut ctx, "live_old", &[2, 5, 7, 9]);
    assume_seq_exprs(
        &mut ctx,
        "live_new",
        &[
            "live_old.index(0)",
            "live_old.index(1)",
            "live_old.index(2)",
            "live_old.index(3)",
            "fresh",
        ],
    );

    ctx.push_assume("fresh_val", "fresh == 11");

    ctx.push_assert("prefix_0", "live_new.index(0) == live_old.index(0)");
    ctx.push_assert("prefix_1", "live_new.index(1) == live_old.index(1)");
    ctx.push_assert("prefix_2", "live_new.index(2) == live_old.index(2)");
    ctx.push_assert("prefix_3", "live_new.index(3) == live_old.index(3)");
    ctx.push_assert("fresh_at_new_tail", "live_new.index(4) == fresh");
    ctx.push_assert(
        "sum_splits_old_plus_fresh",
        "live_new.index(0) + live_new.index(1) + live_new.index(2) + live_new.index(3) + live_new.index(4) == live_old.index(0) + live_old.index(1) + live_old.index(2) + live_old.index(3) + fresh",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79b: post-resize logical prefix should verify, got: {:?}",
        result,
    );
}

/// Tier 79b: a strictly increasing live prefix stays ordered after the resize copy.
#[test]
fn test_vt_tier79b_resize_preserves_prefix_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fresh", "i64");

    assume_seq_i64(&mut ctx, "live_old", &[2, 5, 7, 9]);
    assume_seq_exprs(
        &mut ctx,
        "live_new",
        &[
            "live_old.index(0)",
            "live_old.index(1)",
            "live_old.index(2)",
            "live_old.index(3)",
            "fresh",
        ],
    );

    ctx.push_assume("fresh_val", "fresh == 11");
    ctx.push_assert("old_01", "live_old.index(0) < live_old.index(1)");
    ctx.push_assert("old_12", "live_old.index(1) < live_old.index(2)");
    ctx.push_assert("old_23", "live_old.index(2) < live_old.index(3)");
    ctx.push_assert("new_01", "live_new.index(0) < live_new.index(1)");
    ctx.push_assert("new_12", "live_new.index(1) < live_new.index(2)");
    ctx.push_assert("new_23", "live_new.index(2) < live_new.index(3)");
    ctx.push_assert(
        "fresh_extends_order",
        "live_new.index(3) < live_new.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79b: resize should preserve live-prefix order, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Amortized accounting
// ========================================================================

/// Tier 79c: a dense append without resize has amortized cost 3 under `2*len - cap`.
#[test]
fn test_vt_tier79c_dense_push_has_amortized_cost_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("len_old", "i64");
    ctx.declare_var_parsed("len_new", "i64");
    ctx.declare_var_parsed("cap", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume("len_old_val", "len_old == 3");
    ctx.push_assume("len_new_val", "len_new == 4");
    ctx.push_assume("cap_val", "cap == 4");
    ctx.push_assume("actual_val", "actual == 1");
    ctx.push_assume(
        "potential_old_def",
        "potential_old == len_old + len_old - cap",
    );
    ctx.push_assume(
        "potential_new_def",
        "potential_new == len_new + len_new - cap",
    );
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    ctx.push_assert("dense_before_push", "len_old + len_old >= cap");
    ctx.push_assert("push_increments_len", "len_new == len_old + 1");
    ctx.push_assert(
        "potential_rises_by_two",
        "potential_new == potential_old + 2",
    );
    ctx.push_assert("amortized_three", "amortized == 3");
    ctx.push_assert(
        "potential_stays_nonnegative",
        "potential_old >= 0 && potential_new >= 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79c: dense push amortized cost should verify, got: {:?}",
        result,
    );
}

/// Tier 79c: a full resize append also has amortized cost 3 after the potential drop.
#[test]
fn test_vt_tier79c_full_resize_push_has_amortized_cost_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("len_old", "i64");
    ctx.declare_var_parsed("len_new", "i64");
    ctx.declare_var_parsed("cap_old", "i64");
    ctx.declare_var_parsed("cap_new", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume("len_old_val", "len_old == 4");
    ctx.push_assume("len_new_val", "len_new == 5");
    ctx.push_assume("cap_old_val", "cap_old == 4");
    ctx.push_assume("cap_new_val", "cap_new == 8");
    ctx.push_assume("actual_val", "actual == 5");
    ctx.push_assume(
        "potential_old_def",
        "potential_old == len_old + len_old - cap_old",
    );
    ctx.push_assume(
        "potential_new_def",
        "potential_new == len_new + len_new - cap_new",
    );
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    ctx.push_assert("resize_starts_full", "len_old == cap_old");
    ctx.push_assert("capacity_doubles", "cap_new == cap_old + cap_old");
    ctx.push_assert("resize_copy_cost", "actual == len_old + 1");
    ctx.push_assert("potential_drops", "potential_new < potential_old");
    ctx.push_assert("amortized_three", "amortized == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 79c: full resize amortized cost should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 79d NEGATIVE: a full push cannot keep the old capacity and still fit the new length.
#[test]
fn test_vt_tier79d_full_push_without_growth_is_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("len_new", "u64");
    ctx.declare_var_parsed("cap_new", "u64");

    ctx.push_assume("len_new_val", "len_new == 5");
    ctx.push_assume("cap_new_val", "cap_new == 4");

    ctx.push_assert("new_len_fits", "len_new <= cap_new");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 79d SOUNDNESS: full push without growth must be rejected, got: {:?}",
        result,
    );
}

/// Tier 79d NEGATIVE: dropping one copied element during resize is unsound.
#[test]
fn test_vt_tier79d_missing_copied_element_is_rejected() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "live_old", &[2, 5, 7, 9]);
    assume_seq_i64(&mut ctx, "live_new_wrong", &[2, 5, 0, 9, 11]);

    ctx.push_assert("copied_0", "live_new_wrong.index(0) == live_old.index(0)");
    ctx.push_assert("copied_1", "live_new_wrong.index(1) == live_old.index(1)");
    ctx.push_assert("copied_2", "live_new_wrong.index(2) == live_old.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 79d SOUNDNESS: missing copied element must be rejected, got: {:?}",
        result,
    );
}

/// Tier 79d NEGATIVE: after accounting for the potential drop, charging the full resize cost is too strong.
#[test]
fn test_vt_tier79d_charging_full_resize_cost_is_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("len_old", "i64");
    ctx.declare_var_parsed("len_new", "i64");
    ctx.declare_var_parsed("cap_old", "i64");
    ctx.declare_var_parsed("cap_new", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume("len_old_val", "len_old == 4");
    ctx.push_assume("len_new_val", "len_new == 5");
    ctx.push_assume("cap_old_val", "cap_old == 4");
    ctx.push_assume("cap_new_val", "cap_new == 8");
    ctx.push_assume("actual_val", "actual == 5");
    ctx.push_assume(
        "potential_old_def",
        "potential_old == len_old + len_old - cap_old",
    );
    ctx.push_assume(
        "potential_new_def",
        "potential_new == len_new + len_new - cap_new",
    );
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    ctx.push_assert("wrong_charge", "amortized == actual");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 79d SOUNDNESS: charging full resize cost must be rejected, got: {:?}",
        result,
    );
}
