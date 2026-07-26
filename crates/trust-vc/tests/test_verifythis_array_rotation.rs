// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 83 — In-Place Array Rotation by Reversal VCs.
//!
//! Left-rotating an array by `k` positions using three reversals is a
//! classic in-place algorithm:
//!   Phase 1: reverse a[0 .. k]
//!   Phase 2: reverse a[k .. n]
//!   Phase 3: reverse a[0 .. n]
//!
//! After all three phases, `final[i] == original[(i + k) mod n]`.
//!
//! Concrete 5-element rotation (k = 2):
//!
//!   original      = [10, 20, 30, 40, 50]
//!   after phase 1 = [20, 10, 30, 40, 50]   reverse [0..2]
//!   after phase 2 = [20, 10, 50, 40, 30]   reverse [2..5]
//!   after phase 3 = [30, 40, 50, 10, 20]   reverse [0..5]
//!
//! Rotation check: [30, 40, 50, 10, 20] == original left-rotated by 2 ✓
//!
//! 11 tests: 8 positive (reversal steps, phase postconditions, end-to-end
//!           rotation, permutation sum, chained symbolic composition)
//!         + 3 negatives (skip phase, wrong k, wrong reversal bounds).
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

// ========================================================================
// GROUP A: Single reversal step correctness
// ========================================================================

/// Tier 83a: reversing a 2-element segment swaps its elements.
#[test]
fn test_vt_tier83a_reverse_two_element_segment() {
    let mut ctx = VerificationContext::new();

    // original segment [0..2] = [10, 20]
    assume_seq_i64(&mut ctx, "seg_before", &[10, 20]);
    // reversed segment = [20, 10]
    assume_seq_exprs(
        &mut ctx,
        "seg_after",
        &["seg_before.index(1)", "seg_before.index(0)"],
    );

    ctx.push_assert("swap_0", "seg_after.index(0) == seg_before.index(1)");
    ctx.push_assert("swap_1", "seg_after.index(1) == seg_before.index(0)");
    ctx.push_assert("len_preserved", "seg_after.len() == seg_before.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83a: 2-element reversal should verify, got: {:?}",
        result,
    );
}

/// Tier 83a: reversing a 3-element segment swaps outer elements, keeps middle.
#[test]
fn test_vt_tier83a_reverse_three_element_segment() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "seg_before", &[30, 40, 50]);
    assume_seq_exprs(
        &mut ctx,
        "seg_after",
        &[
            "seg_before.index(2)",
            "seg_before.index(1)",
            "seg_before.index(0)",
        ],
    );

    ctx.push_assert("outer_swap_0", "seg_after.index(0) == seg_before.index(2)");
    ctx.push_assert("middle_stays", "seg_after.index(1) == seg_before.index(1)");
    ctx.push_assert("outer_swap_2", "seg_after.index(2) == seg_before.index(0)");
    ctx.push_assert("len_preserved", "seg_after.len() == seg_before.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83a: 3-element reversal should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Phase postconditions (multi-phase algorithm)
// ========================================================================

/// Tier 83b: Phase 1 — reverse first k=2 elements, rest unchanged.
#[test]
fn test_vt_tier83b_phase1_reverse_first_k_elements() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    // Phase 1 reverses [0..2]: swap indices 0 and 1
    assume_seq_exprs(
        &mut ctx,
        "after_p1",
        &[
            "orig.index(1)",
            "orig.index(0)",
            "orig.index(2)",
            "orig.index(3)",
            "orig.index(4)",
        ],
    );

    // Reversed segment
    ctx.push_assert("rev_0", "after_p1.index(0) == orig.index(1)");
    ctx.push_assert("rev_1", "after_p1.index(1) == orig.index(0)");
    // Unchanged tail
    ctx.push_assert("tail_2", "after_p1.index(2) == orig.index(2)");
    ctx.push_assert("tail_3", "after_p1.index(3) == orig.index(3)");
    ctx.push_assert("tail_4", "after_p1.index(4) == orig.index(4)");
    ctx.push_assert("len_same", "after_p1.len() == orig.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83b: phase 1 reversal should verify, got: {:?}",
        result,
    );
}

/// Tier 83b: Phase 2 — reverse last n-k=3 elements, first k unchanged.
#[test]
fn test_vt_tier83b_phase2_reverse_last_nk_elements() {
    let mut ctx = VerificationContext::new();

    // State after phase 1: [20, 10, 30, 40, 50]
    assume_seq_i64(&mut ctx, "after_p1", &[20, 10, 30, 40, 50]);
    // Phase 2 reverses [2..5]: reverse [30, 40, 50] → [50, 40, 30]
    assume_seq_exprs(
        &mut ctx,
        "after_p2",
        &[
            "after_p1.index(0)",
            "after_p1.index(1)",
            "after_p1.index(4)",
            "after_p1.index(3)",
            "after_p1.index(2)",
        ],
    );

    // Unchanged prefix
    ctx.push_assert("head_0", "after_p2.index(0) == after_p1.index(0)");
    ctx.push_assert("head_1", "after_p2.index(1) == after_p1.index(1)");
    // Reversed tail segment
    ctx.push_assert("rev_2", "after_p2.index(2) == after_p1.index(4)");
    ctx.push_assert("rev_3", "after_p2.index(3) == after_p1.index(3)");
    ctx.push_assert("rev_4", "after_p2.index(4) == after_p1.index(2)");
    ctx.push_assert("len_same", "after_p2.len() == after_p1.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83b: phase 2 reversal should verify, got: {:?}",
        result,
    );
}

/// Tier 83b: Phase 3 — full reverse produces the left rotation.
#[test]
fn test_vt_tier83b_phase3_full_reverse_produces_rotation() {
    let mut ctx = VerificationContext::new();

    // State after phase 2: [20, 10, 50, 40, 30]
    assume_seq_i64(&mut ctx, "after_p2", &[20, 10, 50, 40, 30]);
    // Phase 3 reverses [0..5]: reverse entire array
    assume_seq_exprs(
        &mut ctx,
        "final_arr",
        &[
            "after_p2.index(4)",
            "after_p2.index(3)",
            "after_p2.index(2)",
            "after_p2.index(1)",
            "after_p2.index(0)",
        ],
    );

    ctx.push_assert("rot_0", "final_arr.index(0) == 30");
    ctx.push_assert("rot_1", "final_arr.index(1) == 40");
    ctx.push_assert("rot_2", "final_arr.index(2) == 50");
    ctx.push_assert("rot_3", "final_arr.index(3) == 10");
    ctx.push_assert("rot_4", "final_arr.index(4) == 20");
    ctx.push_assert("len_same", "final_arr.len() == after_p2.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83b: phase 3 full reversal should produce rotation, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: End-to-end rotation properties
// ========================================================================

/// Tier 83c: End-to-end — final[i] == original[(i + k) mod n] for k=2, n=5.
#[test]
fn test_vt_tier83c_end_to_end_rotation_identity() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    // Left rotation by 2: final = [30, 40, 50, 10, 20]
    assume_seq_i64(&mut ctx, "final_arr", &[30, 40, 50, 10, 20]);

    // final[0] == orig[(0+2) mod 5] == orig[2] == 30
    ctx.push_assert("rot_id_0", "final_arr.index(0) == orig.index(2)");
    // final[1] == orig[(1+2) mod 5] == orig[3] == 40
    ctx.push_assert("rot_id_1", "final_arr.index(1) == orig.index(3)");
    // final[2] == orig[(2+2) mod 5] == orig[4] == 50
    ctx.push_assert("rot_id_2", "final_arr.index(2) == orig.index(4)");
    // final[3] == orig[(3+2) mod 5] == orig[0] == 10
    ctx.push_assert("rot_id_3", "final_arr.index(3) == orig.index(0)");
    // final[4] == orig[(4+2) mod 5] == orig[1] == 20
    ctx.push_assert("rot_id_4", "final_arr.index(4) == orig.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83c: end-to-end rotation identity should verify, got: {:?}",
        result,
    );
}

/// Tier 83c: Permutation sum — the rotation preserves the element sum.
#[test]
fn test_vt_tier83c_rotation_preserves_element_sum() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    assume_seq_i64(&mut ctx, "rotated", &[30, 40, 50, 10, 20]);

    ctx.push_assert(
        "sum_preserved",
        "orig.index(0) + orig.index(1) + orig.index(2) + orig.index(3) + orig.index(4) == rotated.index(0) + rotated.index(1) + rotated.index(2) + rotated.index(3) + rotated.index(4)",
    );
    ctx.push_assert("len_preserved", "orig.len() == rotated.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83c: rotation should preserve element sum, got: {:?}",
        result,
    );
}

/// Tier 83c: Chained symbolic — compose all three phases through Seq expressions
/// and verify the rotation identity without hardcoding intermediate arrays.
#[test]
fn test_vt_tier83c_chained_symbolic_three_phase_rotation() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);

    // Phase 1: reverse [0..2] symbolically from orig
    assume_seq_exprs(
        &mut ctx,
        "p1",
        &[
            "orig.index(1)",
            "orig.index(0)",
            "orig.index(2)",
            "orig.index(3)",
            "orig.index(4)",
        ],
    );

    // Phase 2: reverse [2..5] symbolically from p1
    assume_seq_exprs(
        &mut ctx,
        "p2",
        &[
            "p1.index(0)",
            "p1.index(1)",
            "p1.index(4)",
            "p1.index(3)",
            "p1.index(2)",
        ],
    );

    // Phase 3: reverse [0..5] symbolically from p2
    assume_seq_exprs(
        &mut ctx,
        "result",
        &[
            "p2.index(4)",
            "p2.index(3)",
            "p2.index(2)",
            "p2.index(1)",
            "p2.index(0)",
        ],
    );

    // The chained result must satisfy the rotation identity
    ctx.push_assert("chain_rot_0", "result.index(0) == orig.index(2)");
    ctx.push_assert("chain_rot_1", "result.index(1) == orig.index(3)");
    ctx.push_assert("chain_rot_2", "result.index(2) == orig.index(4)");
    ctx.push_assert("chain_rot_3", "result.index(3) == orig.index(0)");
    ctx.push_assert("chain_rot_4", "result.index(4) == orig.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 83c: chained symbolic three-phase rotation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives
// ========================================================================

/// Tier 83d NEGATIVE: skipping phase 2 (not reversing the tail) produces wrong output.
#[test]
fn test_vt_tier83d_skipping_phase2_is_rejected() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    // Phase 1 only: [20, 10, 30, 40, 50], then phase 3 full reverse:
    // reverse [20, 10, 30, 40, 50] → [50, 40, 30, 10, 20]
    // This is NOT a left rotation by 2.
    assume_seq_i64(&mut ctx, "wrong_result", &[50, 40, 30, 10, 20]);

    // Attempt to verify the rotation identity — should fail.
    ctx.push_assert("rot_id_0", "wrong_result.index(0) == orig.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 83d SOUNDNESS: skipping phase 2 must be rejected, got: {:?}",
        result,
    );
}

/// Tier 83d NEGATIVE: rotating by k+1=3 instead of k=2 fails the k=2 identity.
#[test]
fn test_vt_tier83d_wrong_rotation_amount_is_rejected() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    // Left rotation by 3 instead of 2: [40, 50, 10, 20, 30]
    assume_seq_i64(&mut ctx, "wrong_rot", &[40, 50, 10, 20, 30]);

    // Try to verify the k=2 rotation identity
    ctx.push_assert("rot_id_0", "wrong_rot.index(0) == orig.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 83d SOUNDNESS: wrong rotation amount must be rejected, got: {:?}",
        result,
    );
}

/// Tier 83d NEGATIVE: reversing wrong bounds (0..k+1 instead of 0..k) in phase 1.
#[test]
fn test_vt_tier83d_wrong_reversal_bounds_is_rejected() {
    let mut ctx = VerificationContext::new();

    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40, 50]);
    // Wrong phase 1: reverse [0..3] instead of [0..2]
    // [30, 20, 10, 40, 50]
    // Wrong phase 2: reverse [2..5] (using k=2 bounds despite wrong phase 1)
    // [30, 20, 50, 40, 10]
    // Phase 3: reverse [0..5]
    // [10, 40, 50, 20, 30]
    assume_seq_i64(&mut ctx, "wrong_bounds", &[10, 40, 50, 20, 30]);

    // Try to verify the k=2 rotation identity
    ctx.push_assert("rot_id_0", "wrong_bounds.index(0) == orig.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 83d SOUNDNESS: wrong reversal bounds must be rejected, got: {:?}",
        result,
    );
}
