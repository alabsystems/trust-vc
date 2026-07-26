// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 43 - Nonblocking queue core VCs.
//!
//! VerifyThis 2023 included a nonblocking queue challenge. TrustVc does not yet
//! model CAS or heap ownership directly on the stable bridge, so this tier keeps
//! the competition proof shape on the reliable VerificationPipeline path by
//! phrasing the core queue obligations as explicit post-state VCs over a flat
//! linked-list encoding with a dummy sentinel node.
//!
//! Core obligations:
//!   - enqueue links the fresh node at `tail.next` and then swings `tail`
//!   - dequeue returns `head.next` and advances `head`
//!   - empty detection is `head == tail && next[head] == -1`
//!   - helping advances a stale tail to `next[tail]`
//!   - positive queue traces keep payload values symbolic while the fixed
//!     `next` topology captures the queue shape
//!
//! Part of #2187 and #2348.
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
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", values.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, value) in values.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {value}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", exprs.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, expr) in exprs.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {expr}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

fn assume_distinct_i64(ctx: &mut VerificationContext, left: &str, right: &str) {
    let assume_name = format!("{left}_{right}_distinct");
    let assume_cond = format!("{left} != {right}");
    ctx.push_assume(&assume_name, &assume_cond);
}

fn setup_symbolic_empty_enqueue(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("sentinel_value", "i64");
    ctx.declare_var_parsed("fresh_value", "i64");
    assume_distinct_i64(ctx, "sentinel_value", "fresh_value");
    assume_seq_i64(ctx, "next_before", &[-1, -1]);
    assume_seq_i64(ctx, "next_after", &[1, -1]);
    assume_seq_exprs(ctx, "value", &["sentinel_value", "fresh_value"]);
}

fn setup_symbolic_append_queue(ctx: &mut VerificationContext) {
    for name in ["sentinel_value", "front_value", "back_value", "fresh_value"] {
        ctx.declare_var_parsed(name, "i64");
    }
    assume_distinct_i64(ctx, "front_value", "back_value");
    assume_distinct_i64(ctx, "front_value", "fresh_value");
    assume_distinct_i64(ctx, "back_value", "fresh_value");
    assume_seq_i64(ctx, "next_before", &[1, 2, -1, -1]);
    assume_seq_i64(ctx, "next_after", &[1, 2, 3, -1]);
    assume_seq_exprs(
        ctx,
        "value",
        &["sentinel_value", "front_value", "back_value", "fresh_value"],
    );
}

fn setup_symbolic_two_live_queue(ctx: &mut VerificationContext) {
    for name in ["sentinel_value", "front_value", "back_value"] {
        ctx.declare_var_parsed(name, "i64");
    }
    assume_distinct_i64(ctx, "front_value", "back_value");
    assume_seq_i64(ctx, "next", &[1, 2, -1]);
    assume_seq_exprs(
        ctx,
        "value",
        &["sentinel_value", "front_value", "back_value"],
    );
}

fn setup_symbolic_single_live_queue(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("sentinel_value", "i64");
    ctx.declare_var_parsed("front_value", "i64");
    assume_distinct_i64(ctx, "sentinel_value", "front_value");
    assume_seq_i64(ctx, "next", &[1, -1]);
    assume_seq_exprs(ctx, "value", &["sentinel_value", "front_value"]);
}

// ========================================================================
// GROUP A: Enqueue / dequeue core post-states
// ========================================================================

/// Tier 43a: enqueue into an empty logical queue links the first live node.
#[test]
fn test_vt_tier43a_enqueue_into_empty_queue_links_first_node() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_empty_enqueue(&mut ctx);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 0");
    ctx.push_assume("head_after_frame", "head_after == head_before");
    ctx.push_assume("tail_after_new", "tail_after == 1");
    ctx.push_assume("empty_before", "next_before.index(head_before) == -1");
    ctx.push_assume("linked_first", "next_after.index(tail_before) == 1");

    ctx.push_assert("sentinel_stays_head", "head_after == 0");
    ctx.push_assert(
        "tail_swings_to_successor_of_head",
        "tail_after == next_after.index(head_after)",
    );
    ctx.push_assert(
        "front_value_visible",
        "value.index(next_after.index(head_after)) == fresh_value",
    );
    ctx.push_assert(
        "live_node_not_sentinel",
        "value.index(tail_after) != value.index(head_after)",
    );
    ctx.push_assert("new_tail_is_last", "next_after.index(tail_after) == -1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43a: enqueue into empty queue should verify, got: {:?}",
        result,
    );
}

/// Tier 43b: enqueue onto a non-empty queue preserves the old front and appends at the tail.
#[test]
fn test_vt_tier43b_enqueue_preserves_front_and_appends_tail() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_append_queue(&mut ctx);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 2");
    ctx.push_assume("head_after_frame", "head_after == head_before");
    ctx.push_assume("tail_after_new", "tail_after == 3");
    ctx.push_assume("linked_old_tail", "next_after.index(tail_before) == 3");

    ctx.push_assert(
        "front_still_first",
        "value.index(next_after.index(head_after)) == front_value",
    );
    ctx.push_assert(
        "old_tail_still_precedes_new_tail",
        "next_after.index(next_after.index(head_after)) == tail_before",
    );
    ctx.push_assert("new_tail_value", "value.index(tail_after) == fresh_value");
    ctx.push_assert(
        "front_and_new_tail_stay_distinct",
        "value.index(next_after.index(head_after)) != value.index(tail_after)",
    );
    ctx.push_assert("tail_after_is_last", "next_after.index(tail_after) == -1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43b: enqueue should preserve FIFO front and append the tail, got: {:?}",
        result,
    );
}

/// Tier 43c: dequeue from a two-element queue returns the first live node and advances head.
#[test]
fn test_vt_tier43c_dequeue_returns_first_live_node() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_two_live_queue(&mut ctx);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");
    ctx.declare_var_parsed("ret", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 2");
    ctx.push_assume("ret_front", "ret == value.index(next.index(head_before))");
    ctx.push_assume("head_after_step", "head_after == next.index(head_before)");
    ctx.push_assume("tail_after_frame", "tail_after == tail_before");

    ctx.push_assert("dequeued_oldest", "ret == front_value");
    ctx.push_assert(
        "head_now_marks_old_front",
        "value.index(head_after) == front_value",
    );
    ctx.push_assert(
        "next_front_now_second",
        "value.index(next.index(head_after)) == back_value",
    );
    ctx.push_assert(
        "returned_value_differs_from_next_front",
        "ret != value.index(next.index(head_after))",
    );
    ctx.push_assert("tail_stays_last", "next.index(tail_after) == -1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43c: dequeue should return the first live node, got: {:?}",
        result,
    );
}

/// Tier 43d: dequeue from a single-element queue empties the logical queue.
#[test]
fn test_vt_tier43d_singleton_dequeue_empties_queue() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_single_live_queue(&mut ctx);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");
    ctx.declare_var_parsed("ret", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 1");
    ctx.push_assume("ret_front", "ret == value.index(next.index(head_before))");
    ctx.push_assume("head_after_step", "head_after == next.index(head_before)");
    ctx.push_assume("tail_after_step", "tail_after == head_after");

    ctx.push_assert("dequeued_value", "ret == front_value");
    ctx.push_assert(
        "returned_value_is_new_head_payload",
        "ret == value.index(head_after)",
    );
    ctx.push_assert("head_catches_tail", "head_after == tail_after");
    ctx.push_assert("queue_is_empty", "next.index(head_after) == -1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43d: singleton dequeue should empty the queue, got: {:?}",
        result,
    );
}

/// Tier 43e: empty detection returns `NO_TASK` when head and tail both point at the sentinel.
#[test]
fn test_vt_tier43e_empty_queue_reports_no_task() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "next", &[-1]);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");
    ctx.declare_var_parsed("ret", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 0");
    ctx.push_assume("empty_guard", "head_before == tail_before");
    ctx.push_assume("empty_next", "next.index(head_before) == -1");
    ctx.push_assume("head_after_frame", "head_after == head_before");
    ctx.push_assume("tail_after_frame", "tail_after == tail_before");
    ctx.push_assume("ret_empty", "ret == -1");

    ctx.push_assert("still_empty_head", "head_after == 0");
    ctx.push_assert("still_empty_tail", "tail_after == 0");
    ctx.push_assert("sentinel_still_last", "next.index(head_after) == -1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43e: empty queue should report no task, got: {:?}",
        result,
    );
}

/// Tier 43f: a stale tail helps itself forward to the real last node.
#[test]
fn test_vt_tier43f_helping_advances_stale_tail() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_two_live_queue(&mut ctx);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("tail_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("tail_after", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("tail_before_val", "tail_before == 1");
    ctx.push_assume("head_after_frame", "head_after == head_before");
    ctx.push_assume("tail_after_help", "tail_after == next.index(tail_before)");

    ctx.push_assert(
        "front_node_unchanged",
        "value.index(next.index(head_after)) == front_value",
    );
    ctx.push_assert(
        "tail_moves_to_last_payload",
        "value.index(tail_after) == back_value",
    );
    ctx.push_assert(
        "helped_tail_is_past_front",
        "tail_after != next.index(head_after)",
    );
    ctx.push_assert("helped_tail_is_last", "next.index(tail_after) == -1");
    ctx.push_assert(
        "front_and_tail_payloads_stay_distinct",
        "value.index(next.index(head_after)) != value.index(tail_after)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 43f: helping should advance a stale tail, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Soundness negatives
// ========================================================================

/// Tier 43g: dequeue must not skip the first live node.
#[test]
fn test_vt_tier43g_dequeue_must_not_skip_front() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "next", &[1, 2, -1]);
    assume_seq_i64(&mut ctx, "value", &[-99, 10, 20]);
    ctx.declare_var_parsed("head_before", "i64");
    ctx.declare_var_parsed("head_after", "i64");
    ctx.declare_var_parsed("ret", "i64");

    ctx.push_assume("head_before_val", "head_before == 0");
    ctx.push_assume("wrong_ret", "ret == 20");
    ctx.push_assume("wrong_head", "head_after == 2");

    ctx.push_assert(
        "must_return_front",
        "ret == value.index(next.index(head_before))",
    );
    ctx.push_assert("must_advance_once", "head_after == next.index(head_before)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 43g SOUNDNESS: dequeue skipping the front node must be rejected, got: {:?}",
        result,
    );
}

/// Tier 43h: `head == tail` is not enough for emptiness if `next[head]` is live.
#[test]
fn test_vt_tier43h_head_equals_tail_does_not_imply_empty() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "next", &[1, -1]);
    assume_seq_i64(&mut ctx, "value", &[-99, 10]);
    ctx.declare_var_parsed("head", "i64");
    ctx.declare_var_parsed("tail", "i64");
    ctx.declare_var_parsed("ret", "i64");

    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("tail_val", "tail == 0");
    ctx.push_assume("wrong_empty_reply", "ret == -1");

    ctx.push_assert("live_successor_exists", "next.index(head) != -1");
    ctx.push_assert(
        "must_not_report_empty",
        "ret == value.index(next.index(head))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 43h SOUNDNESS: stale-tail empty detection must be rejected, got: {:?}",
        result,
    );
}
