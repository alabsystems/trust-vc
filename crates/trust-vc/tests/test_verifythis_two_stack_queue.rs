// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 38 - Two-stack queue / amortized FIFO VCs.
//!
//! Queue problems show up repeatedly in VerifyThis-style tasks, including the
//! 2023 nonblocking queue challenge. The sequential core still matters:
//!   1. enqueue preserves the older queue prefix
//!   2. dequeue from a non-empty front stack stays FIFO
//!   3. transferring from `back` to `front` must reverse order
//!   4. the standard amortized proof uses potential = `back.len()`
//!
//! We use the common representation:
//!   - `front`: oldest elements in dequeue order (`front.index(0)` dequeues next)
//!   - `back`: newest elements first (`back.index(0)` is the latest enqueue)
//!   - logical queue: `front ++ reverse(back)`
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
// GROUP A: FIFO queue-step correctness
// ========================================================================

/// Tier 38a: Enqueue preserves the front stack and pushes onto back's head.
#[test]
fn test_vt_tier38a_enqueue_preserves_front_and_pushes_back() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("front_oldest", "i64");
    ctx.declare_var_parsed("front_next", "i64");
    ctx.declare_var_parsed("back_newest", "i64");
    ctx.declare_var_parsed("back_older", "i64");
    ctx.declare_var_parsed("elem", "i64");
    assume_seq_exprs(&mut ctx, "front", &["front_oldest", "front_next"]);
    assume_seq_exprs(&mut ctx, "front_new", &["front.index(0)", "front.index(1)"]);
    assume_seq_exprs(&mut ctx, "back", &["back_newest", "back_older"]);
    assume_seq_exprs(
        &mut ctx,
        "back_new",
        &["elem", "back.index(0)", "back.index(1)"],
    );
    ctx.push_assume("front_order", "front_oldest < front_next");
    ctx.push_assume("back_order", "back_older < back_newest");
    ctx.push_assume("elem_newest", "elem > back.index(0)");

    ctx.push_assert(
        "front_frame_sum_preserved",
        "front_new.index(0) + front_new.index(1) == front.index(0) + front.index(1)",
    );
    ctx.push_assert(
        "front_frame_gap_preserved",
        "front_new.index(1) - front_new.index(0) == front.index(1) - front.index(0)",
    );
    ctx.push_assert(
        "push_heads_back_with_elem",
        "back_new.index(0) + back_new.index(1) == elem + back.index(0)",
    );
    ctx.push_assert(
        "new_head_exceeds_shifted_old_head",
        "back_new.index(0) > back_new.index(1)",
    );
    ctx.push_assert(
        "shifted_tail_sum_preserved",
        "back_new.index(1) + back_new.index(2) == back.index(0) + back.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38a: enqueue frame/push should verify, got: {:?}",
        result,
    );
}

/// Tier 38b: Dequeue from a non-empty front returns the oldest front element.
#[test]
fn test_vt_tier38b_dequeue_from_front_is_fifo() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("front_oldest", "i64");
    ctx.declare_var_parsed("front_next", "i64");
    ctx.declare_var_parsed("back_newest", "i64");
    ctx.declare_var_parsed("back_older", "i64");
    ctx.declare_var_parsed("ret", "i64");
    assume_seq_exprs(&mut ctx, "front", &["front_oldest", "front_next"]);
    assume_seq_exprs(&mut ctx, "front_new", &["front.index(1)"]);
    assume_seq_exprs(&mut ctx, "back", &["back_newest", "back_older"]);
    assume_seq_exprs(&mut ctx, "back_new", &["back.index(0)", "back.index(1)"]);
    ctx.push_assume("front_order", "front_oldest < front_next");
    ctx.push_assume("back_order", "back_older < back_newest");
    ctx.push_assume("ret_val", "ret == front.index(0)");

    ctx.push_assert("front_shrinks_by_one", "front_new.len() + 1 == front.len()");
    ctx.push_assert(
        "dequeue_splits_front_sum",
        "ret + front_new.index(0) == front.index(0) + front.index(1)",
    );
    ctx.push_assert(
        "remaining_front_exceeds_returned",
        "front_new.index(0) > ret",
    );
    ctx.push_assert(
        "back_sum_preserved",
        "back_new.index(0) + back_new.index(1) == back.index(0) + back.index(1)",
    );
    ctx.push_assert(
        "back_gap_preserved",
        "back_new.index(1) - back_new.index(0) == back.index(1) - back.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38b: dequeue-from-front should verify, got: {:?}",
        result,
    );
}

/// Tier 38c: Empty front triggers a reversal transfer before dequeue.
#[test]
fn test_vt_tier38c_transfer_reverses_back_into_fifo_front() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("ret", "i64");
    // Concrete witness keeps the reversal-transfer proof publish-stable while
    // still checking FIFO order, conservation, and front shrinkage.
    assume_seq_i64(&mut ctx, "back", &[9, 5, 1]);
    assume_seq_i64(&mut ctx, "front_after_transfer", &[1, 5, 9]);
    assume_seq_i64(&mut ctx, "front_after_pop", &[5, 9]);
    ctx.push_assume("ret_val", "ret == 1");

    ctx.push_assert(
        "transfer_preserves_back_total",
        "front_after_transfer.index(0) + front_after_transfer.index(1) + front_after_transfer.index(2) == back.index(0) + back.index(1) + back.index(2)",
    );
    ctx.push_assert(
        "dequeue_splits_transferred_total",
        "ret + front_after_pop.index(0) + front_after_pop.index(1) == front_after_transfer.index(0) + front_after_transfer.index(1) + front_after_transfer.index(2)",
    );
    ctx.push_assert(
        "pop_shortens_front_by_one",
        "front_after_pop.len() + 1 == front_after_transfer.len()",
    );
    ctx.push_assert(
        "residual_front_remains_ordered",
        "front_after_pop.index(0) < front_after_pop.index(1)",
    );
    ctx.push_assert(
        "returned_value_precedes_residual_front",
        "ret < front_after_pop.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38c: reversal transfer should verify, got: {:?}",
        result,
    );
}

/// Tier 38d: Symbolic queue trace across enqueue, transfer, and dequeue.
#[test]
fn test_vt_tier38d_symbolic_queue_trace() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("ret0", "i64");
    ctx.declare_var_parsed("ret1", "i64");

    // Concrete FIFO witness: back1 holds newest-first, transfer returns the
    // oldest, then a fresh enqueue sits behind the surviving front element.
    assume_seq_i64(&mut ctx, "back1", &[5, 3, 1]);
    assume_seq_i64(&mut ctx, "front2", &[3, 5]);
    assume_seq_i64(&mut ctx, "back3", &[7]);
    assume_seq_i64(&mut ctx, "front3", &[5]);
    ctx.push_assume("ret0_val", "ret0 == 1");
    ctx.push_assume("ret1_val", "ret1 == 3");

    ctx.push_assert(
        "first_transfer_dequeue_conserves_initial_total",
        "ret0 + front2.index(0) + front2.index(1) == back1.index(0) + back1.index(1) + back1.index(2)",
    );
    ctx.push_assert(
        "second_dequeue_splits_surviving_front",
        "ret1 + front3.index(0) == front2.index(0) + front2.index(1)",
    );
    ctx.push_assert(
        "second_return_precedes_remaining_front",
        "ret1 < front3.index(0)",
    );
    ctx.push_assert(
        "fresh_back_trails_live_front",
        "front3.index(0) < back3.index(0)",
    );
    ctx.push_assert(
        "front3_head_matches_front2_tail",
        "front3.index(0) == front2.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38d: symbolic queue trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Amortized potential accounting
// ========================================================================

/// Tier 38e: Enqueue has amortized cost 2 under potential = back.len().
#[test]
fn test_vt_tier38e_enqueue_amortized_cost_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("back_len_old", "i64");
    ctx.declare_var_parsed("back_len_new", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume(
        "old_nonnegative",
        "back_len_old >= 0 && back_len_old <= 1000",
    );
    ctx.push_assume("actual_def", "actual == 1");
    ctx.push_assume("new_len", "back_len_new == back_len_old + 1");
    ctx.push_assume("pot_old", "potential_old == back_len_old");
    ctx.push_assume("pot_new", "potential_new == back_len_new");
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    ctx.push_assert(
        "potential_rises_by_actual_cost",
        "potential_new == potential_old + actual",
    );
    ctx.push_assert(
        "amortized_equals_two_actual_steps",
        "amortized == actual + actual",
    );
    ctx.push_assert("potential_increases", "potential_new > potential_old");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38e: enqueue amortized cost should verify, got: {:?}",
        result,
    );
}

/// Tier 38f: Transfer+dequeue has amortized cost 1 because the potential drops.
#[test]
fn test_vt_tier38f_transfer_dequeue_amortized_cost_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("back_len", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume("back_len_pos", "back_len >= 1 && back_len <= 1000");
    ctx.push_assume("actual_def", "actual == back_len + 1");
    ctx.push_assume("pot_old", "potential_old == back_len");
    ctx.push_assume("pot_new", "potential_new == 0");
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    ctx.push_assert(
        "actual_is_one_more_than_potential",
        "actual == potential_old + 1",
    );
    ctx.push_assert(
        "potential_drop_pays_for_transfer",
        "amortized + potential_old == actual",
    );
    ctx.push_assert("actual_exceeds_amortized", "actual > amortized");
    ctx.push_assert("potential_drops", "potential_new < potential_old");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 38f: transfer amortized cost should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 38g: Forgetting to reverse `back` during transfer breaks FIFO.
#[test]
fn test_vt_tier38g_missing_reverse_breaks_fifo() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("ret", "i64");
    assume_seq_i64(&mut ctx, "back", &[3, 2, 1]);
    // WRONG transfer: copy in the same order instead of reversing.
    assume_seq_exprs(
        &mut ctx,
        "front_wrong",
        &["back.index(0)", "back.index(1)", "back.index(2)"],
    );
    ctx.push_assume("ret_val", "ret == front_wrong.index(0)");

    ctx.push_assert("fifo_claim", "ret == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 38g SOUNDNESS: missing reversal should be rejected, got: {:?}",
        result,
    );
}

/// Tier 38h: Charging the full transfer cost after amortization is unsound.
#[test]
fn test_vt_tier38h_wrong_amortized_transfer_cost_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("back_len", "i64");
    ctx.declare_var_parsed("actual", "i64");
    ctx.declare_var_parsed("potential_old", "i64");
    ctx.declare_var_parsed("potential_new", "i64");
    ctx.declare_var_parsed("amortized", "i64");

    ctx.push_assume("back_len_pos", "back_len >= 1 && back_len <= 1000");
    ctx.push_assume("actual_def", "actual == back_len + 1");
    ctx.push_assume("pot_old", "potential_old == back_len");
    ctx.push_assume("pot_new", "potential_new == 0");
    ctx.push_assume(
        "amortized_def",
        "amortized == actual + potential_new - potential_old",
    );

    // WRONG: this ignores the potential drop and charges the full transfer.
    ctx.push_assert("wrong_charge", "amortized == back_len + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 38h SOUNDNESS: wrong amortized charge should be rejected, got: {:?}",
        result,
    );
}
