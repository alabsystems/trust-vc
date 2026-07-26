// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 61 - Fisher-Yates shuffle step VCs.
//!
//! Fisher-Yates shuffle iterates from the tail toward the head. At each step it:
//!   - chooses `j` with `0 <= j <= i`
//!   - swaps `a[i]` with `a[j]`
//!   - decrements `i`, freezing one more suffix cell
//!
//! Competition proofs usually need only the local obligations:
//!   - sampled indices stay inside the active prefix
//!   - the step is a two-position swap with a frame on all other cells
//!   - later iterations preserve the already-fixed suffix
//!   - overwrite-style bugs and out-of-range picks are rejected
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
// GROUP A: Index bounds and self-swap entry cases
// ========================================================================

/// Tier 61a: the sampled index stays inside the active prefix.
#[test]
fn test_vt_tier61a_pick_stays_within_active_prefix() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");

    ctx.push_assume("n_val", "n == 5");
    ctx.push_assume("i_val", "i == 4");
    ctx.push_assume("j_val", "j == 1");

    ctx.push_assert("pick_in_prefix", "j <= i");
    ctx.push_assert("active_index_in_bounds", "i < n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61a: pick inside active prefix should verify, got: {:?}",
        result,
    );
}

/// Tier 61a: choosing the current tail performs a self-swap and preserves the array.
#[test]
fn test_vt_tier61a_self_swap_preserves_array() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "a_post", &[10, 20, 30, 40]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("j_val", "j == 2");

    ctx.push_assert("self_swap_choice", "j == i");
    ctx.push_assert("cell_0_preserved", "a_post.index(0) == a_pre.index(0)");
    ctx.push_assert("cell_1_preserved", "a_post.index(1) == a_pre.index(1)");
    ctx.push_assert("cell_i_preserved", "a_post.index(i) == a_pre.index(i)");
    ctx.push_assert("tail_preserved", "a_post.index(3) == a_pre.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61a: self-swap should preserve the array, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Single-step swap semantics
// ========================================================================

/// Tier 61b: swapping a sampled prefix cell into the tail fixes that suffix cell.
#[test]
fn test_vt_tier61b_tail_swap_moves_sample_to_fixed_suffix() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "a_post", &[10, 40, 30, 20]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 3");
    ctx.push_assume("j_val", "j == 1");

    ctx.push_assert("choice_is_strict_prefix", "j < i");
    ctx.push_assert(
        "sampled_value_moves_to_tail",
        "a_post.index(i) == a_pre.index(j)",
    );
    ctx.push_assert("tail_value_moves_back", "a_post.index(j) == a_pre.index(i)");
    ctx.push_assert("prefix_frame_0", "a_post.index(0) == a_pre.index(0)");
    ctx.push_assert("prefix_frame_2", "a_post.index(2) == a_pre.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61b: tail swap should verify, got: {:?}",
        result,
    );
}

/// Tier 61b: only the two chosen positions change during the swap.
#[test]
fn test_vt_tier61b_swap_has_two_cell_frame() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 20, 30, 40, 50]);
    assume_seq_i64(&mut ctx, "a_post", &[10, 40, 30, 20, 50]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 3");
    ctx.push_assume("j_val", "j == 1");

    ctx.push_assert("swap_hi", "a_post.index(i) == a_pre.index(j)");
    ctx.push_assert("swap_lo", "a_post.index(j) == a_pre.index(i)");
    ctx.push_assert("frame_0", "a_post.index(0) == a_pre.index(0)");
    ctx.push_assert("frame_2", "a_post.index(2) == a_pre.index(2)");
    ctx.push_assert("frame_4", "a_post.index(4) == a_pre.index(4)");
    ctx.push_assert("len_preserved", "a_post.len() == a_pre.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61b: swap frame should verify, got: {:?}",
        result,
    );
}

/// Tier 61b: the fixed suffix may already contain earlier shuffled values.
#[test]
fn test_vt_tier61b_swap_preserves_existing_fixed_suffix() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 40, 30, 20, 50]);
    assume_seq_i64(&mut ctx, "a_post", &[30, 40, 10, 20, 50]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("j_val", "j == 0");

    ctx.push_assert(
        "swap_to_new_suffix_cell",
        "a_post.index(i) == a_pre.index(j)",
    );
    ctx.push_assert(
        "chosen_value_moves_forward",
        "a_post.index(j) == a_pre.index(i)",
    );
    ctx.push_assert(
        "older_suffix_cell_3_frozen",
        "a_post.index(3) == a_pre.index(3)",
    );
    ctx.push_assert(
        "older_suffix_cell_4_frozen",
        "a_post.index(4) == a_pre.index(4)",
    );
    ctx.push_assert("middle_frame", "a_post.index(1) == a_pre.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61b: older fixed suffix should stay frozen, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Multi-step local invariants
// ========================================================================

/// Tier 61c: a later iteration keeps the suffix fixed by the previous one.
#[test]
fn test_vt_tier61c_later_iteration_preserves_previous_suffix() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "step1", &[10, 40, 30, 20]);
    assume_seq_i64(&mut ctx, "step2", &[30, 40, 10, 20]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("j_val", "j == 0");

    ctx.push_assert("new_suffix_cell_filled", "step2.index(i) == step1.index(j)");
    ctx.push_assert(
        "prefix_value_swapped_out",
        "step2.index(j) == step1.index(i)",
    );
    ctx.push_assert("previous_suffix_frozen", "step2.index(3) == step1.index(3)");
    ctx.push_assert(
        "other_prefix_cell_framed",
        "step2.index(1) == step1.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61c: later iteration should preserve previous suffix, got: {:?}",
        result,
    );
}

/// Tier 61c: after concrete steps, the result is still a length-preserving permutation.
#[test]
fn test_vt_tier61c_concrete_two_step_permutation() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "after", &[30, 40, 10, 20]);

    ctx.push_assert("len_preserved", "after.len() == orig.len()");
    ctx.push_assert(
        "after_0_maps_from_orig_2",
        "after.index(0) == orig.index(2)",
    );
    ctx.push_assert(
        "after_1_maps_from_orig_3",
        "after.index(1) == orig.index(3)",
    );
    ctx.push_assert(
        "after_2_maps_from_orig_0",
        "after.index(2) == orig.index(0)",
    );
    ctx.push_assert(
        "after_3_maps_from_orig_1",
        "after.index(3) == orig.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61c: concrete permutation should verify, got: {:?}",
        result,
    );
}

/// Tier 61c: the final step only touches the remaining two-cell prefix.
#[test]
fn test_vt_tier61c_final_step_keeps_completed_suffix() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[30, 40, 10, 20]);
    assume_seq_i64(&mut ctx, "a_post", &[40, 30, 10, 20]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 1");
    ctx.push_assume("j_val", "j == 0");

    ctx.push_assert("last_swap_front", "a_post.index(j) == a_pre.index(i)");
    ctx.push_assert("last_swap_back", "a_post.index(i) == a_pre.index(j)");
    ctx.push_assert("suffix_cell_2_frozen", "a_post.index(2) == a_pre.index(2)");
    ctx.push_assert("suffix_cell_3_frozen", "a_post.index(3) == a_pre.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 61c: final step should keep completed suffix fixed, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 61d NEGATIVE: the sampled index may not fall outside the active prefix.
#[test]
fn test_vt_tier61d_out_of_range_pick_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");

    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("j_val", "j == 3");

    ctx.push_assert("pick_in_prefix", "j <= i");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 61d SOUNDNESS: out-of-range pick must fail, got: {:?}",
        result,
    );
}

/// Tier 61d NEGATIVE: overwriting the tail instead of swapping loses a value.
#[test]
fn test_vt_tier61d_overwrite_instead_of_swap_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "a_bad", &[10, 20, 30, 20]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 3");
    ctx.push_assume("j_val", "j == 1");

    ctx.push_assert("tail_gets_sample", "a_bad.index(i) == a_pre.index(j)");
    ctx.push_assert("sample_slot_gets_tail", "a_bad.index(j) == a_pre.index(i)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 61d SOUNDNESS: overwrite-only update must fail, got: {:?}",
        result,
    );
}

/// Tier 61d NEGATIVE: later iterations must not mutate an already-fixed suffix cell.
#[test]
fn test_vt_tier61d_mutating_fixed_suffix_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "step1", &[10, 40, 30, 20]);
    assume_seq_i64(&mut ctx, "step2_bad", &[30, 40, 10, 99]);

    ctx.push_assert(
        "fixed_suffix_preserved",
        "step2_bad.index(3) == step1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 61d SOUNDNESS: mutating a fixed suffix cell must fail, got: {:?}",
        result,
    );
}

/// Tier 61d NEGATIVE: non-chosen cells must satisfy the frame condition.
#[test]
fn test_vt_tier61d_wrong_frame_cell_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[10, 20, 30, 40, 50]);
    assume_seq_i64(&mut ctx, "a_bad", &[99, 40, 30, 20, 50]);

    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.push_assume("i_val", "i == 3");
    ctx.push_assume("j_val", "j == 1");

    ctx.push_assert("swap_hi", "a_bad.index(i) == a_pre.index(j)");
    ctx.push_assert("swap_lo", "a_bad.index(j) == a_pre.index(i)");
    ctx.push_assert("frame_0", "a_bad.index(0) == a_pre.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 61d SOUNDNESS: changing a framed cell must fail, got: {:?}",
        result,
    );
}
