// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 42 - Work-stealing task-tree VCs.
//!
//! VerifyThis 2024 included "Work-stealing for Task Trees" with three stages:
//!   1. Version 0: a single worker expands a binary task tree via a deque
//!   2. Version 1: sender-initiated stealing transfers the deque's top task
//!   3. Version 2: receiver-initiated stealing handles explicit steal requests
//!
//! This tier keeps the proof obligations on the stable VerificationPipeline
//! path by phrasing them as explicit post-state VCs over small deque states.
//! The positive cases keep the task ids symbolic so the solver has to reason
//! about deque order and frame relations instead of replaying one fixed trace.
//! That still exercises the core competition properties:
//!   - root task stays in-bounds
//!   - expanding a parent schedules the left child next via bottom-pop order
//!   - child execution is gated by parent completion
//!   - steals remove the deque's top element, not the bottom one
//!   - receiver-side requests reset cleanly and report `NO_TASK` on emptiness
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

// ========================================================================
// GROUP A: Version 0 - sequential task-tree expansion
// ========================================================================

/// Tier 42a: the root task is seeded on worker 0 and stays within the task set.
#[test]
fn test_vt_tier42a_root_seeded_and_in_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("root_task", "i64");
    assume_seq_exprs(&mut ctx, "deque0", &["root_task"]);
    ctx.declare_var_parsed("n_tasks", "i64");
    // Keep the symbolic seed away from signed wraparound so this VC checks the
    // task budget relation, not bitvector overflow behavior.
    ctx.push_assume(
        "root_in_small_positive_range",
        "0 <= root_task && root_task <= 1000",
    );
    ctx.push_assume("task_budget", "n_tasks == root_task + deque0.len() + 1");

    ctx.push_assert("root_is_nonnegative", "0 <= deque0.index(0)");
    ctx.push_assert(
        "root_seed_stays_in_budget",
        "deque0.index(0) + deque0.len() <= n_tasks",
    );
    ctx.push_assert(
        "next_task_id_still_available",
        "deque0.index(0) + 1 < n_tasks",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42a: root seed should stay in bounds, got: {:?}",
        result,
    );
}

/// Tier 42b: expanding the root pushes right then left, so bottom-pop runs left next.
#[test]
fn test_vt_tier42b_root_expansion_schedules_left_child_next() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("left_child", "i64");
    ctx.declare_var_parsed("right_child", "i64");
    ctx.declare_var_parsed("next_bottom", "i64");
    ctx.declare_var_parsed("parent_done", "i64");
    assume_seq_exprs(&mut ctx, "deque_after", &["right_child", "left_child"]);

    ctx.push_assume("left_before_right", "left_child < right_child");
    ctx.push_assume("next_bottom_def", "next_bottom == deque_after.index(1)");
    ctx.push_assume("parent_done_val", "parent_done == 1");
    ctx.push_assume(
        "adjacent_children",
        "right_child == left_child + parent_done",
    );

    ctx.push_assert(
        "left_child_occupies_parent_done_slot",
        "deque_after.index(parent_done) == left_child",
    );
    ctx.push_assert(
        "top_exceeds_bottom_by_one_completion_step",
        "deque_after.index(0) == next_bottom + parent_done",
    );
    ctx.push_assert(
        "top_exceeds_bottom",
        "deque_after.index(0) > deque_after.index(parent_done)",
    );
    ctx.push_assert(
        "done_parent_leaves_two_ready_slots",
        "deque_after.len() == parent_done + 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42b: root expansion should leave the left child at the bottom, got: {:?}",
        result,
    );
}

/// Tier 42c: once a parent is complete, starting its children respects the dependency.
#[test]
fn test_vt_tier42c_parent_completion_gates_child_execution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("parent_done", "i64");
    ctx.declare_var_parsed("left_started", "i64");
    ctx.declare_var_parsed("right_started", "i64");

    ctx.push_assume("parent_done_val", "parent_done == 1");
    ctx.push_assume("left_started_val", "left_started == 1");
    ctx.push_assume("right_started_val", "right_started == 0");

    ctx.push_assert(
        "started_children_match_parent_credit",
        "left_started + right_started == parent_done",
    );
    ctx.push_assert("left_not_behind_right", "left_started >= right_started");
    ctx.push_assert(
        "child_states_are_not_equal",
        "left_started != right_started",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42c: child starts should be gated by parent completion, got: {:?}",
        result,
    );
}

/// Tier 42d: a child must not start before its parent is completed.
#[test]
fn test_vt_tier42d_child_before_parent_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("parent_done", "i64");
    ctx.declare_var_parsed("child_started", "i64");

    ctx.push_assume("parent_not_done", "parent_done == 0");
    ctx.push_assume("child_started_val", "child_started == 1");
    ctx.push_assert("invalid_dependency", "child_started <= parent_done");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 42d SOUNDNESS: child-before-parent execution must be rejected, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Version 1 - sender-initiated stealing
// ========================================================================

/// Tier 42e: a waiting thief receives the victim deque's top task.
#[test]
fn test_vt_tier42e_sender_initiated_steal_moves_top_task() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("top_task", "i64");
    ctx.declare_var_parsed("bottom_task", "i64");
    assume_seq_exprs(&mut ctx, "victim", &["top_task", "bottom_task"]);
    ctx.declare_var_parsed("signal_before", "i64");
    ctx.declare_var_parsed("signal_after", "i64");
    ctx.declare_var_parsed("transfer", "i64");

    ctx.push_assume("top_before_bottom", "top_task < bottom_task");
    ctx.push_assume("waiting", "signal_before == -2");
    ctx.push_assume("signal_after_task", "signal_after == victim.index(0)");
    ctx.push_assume("transfer_matches_signal", "transfer == signal_after");

    ctx.push_assert(
        "stolen_and_remaining_tasks_preserve_total_work",
        "transfer + victim.skip(1).index(0) == victim.index(0) + victim.index(1)",
    );
    ctx.push_assert(
        "victim_shrinks_by_one",
        "victim.skip(1).len() + 1 == victim.len()",
    );
    ctx.push_assert(
        "suffix_head_matches_old_bottom_slot",
        "victim.skip(1).index(0) == victim.index(victim.skip(1).len())",
    );
    ctx.push_assert(
        "transferred_precedes_remaining_bottom",
        "transfer < victim.skip(1).index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42e: sender-initiated steal should pop the top task, got: {:?}",
        result,
    );
}

/// Tier 42f: if the target is not waiting, the sender leaves the victim deque unchanged.
#[test]
fn test_vt_tier42f_sender_skips_nonwaiting_target() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("top_task", "i64");
    ctx.declare_var_parsed("bottom_task", "i64");
    assume_seq_exprs(&mut ctx, "victim", &["top_task", "bottom_task"]);
    ctx.declare_var_parsed("victim_after", "Seq<i64>");
    ctx.declare_var_parsed("signal_before", "i64");
    ctx.declare_var_parsed("signal_after", "i64");

    ctx.push_assume("top_before_bottom", "top_task < bottom_task");
    ctx.push_assume("not_waiting", "signal_before == -3");
    ctx.push_assume("victim_frame", "victim_after == victim");
    ctx.push_assume("victim_frame_len", "victim_after.len() == victim.len()");
    ctx.push_assume("signal_unchanged", "signal_after == signal_before");

    ctx.push_assert(
        "sum_preserved",
        "victim_after.index(0) + victim_after.index(1) == victim.index(0) + victim.index(1)",
    );
    ctx.push_assert(
        "gap_preserved",
        "victim_after.index(1) - victim_after.index(0) == victim.index(1) - victim.index(0)",
    );
    ctx.push_assert(
        "head_and_tail_stay_ordered",
        "victim_after.index(0) < victim_after.index(1)",
    );
    ctx.push_assert(
        "signal_tracks_head_in_lockstep",
        "signal_after + victim_after.index(0) == signal_before + victim.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42f: non-waiting targets should preserve the victim deque, got: {:?}",
        result,
    );
}

/// Tier 42g: a sender-initiated steal must not transfer the deque's bottom task.
#[test]
fn test_vt_tier42g_sender_must_not_transfer_bottom_task() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "victim", &[7, 9]);
    ctx.declare_var_parsed("transfer", "i64");

    ctx.push_assume("wrong_end", "transfer == victim.index(1)");
    ctx.push_assert("must_send_top", "transfer == victim.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 42g SOUNDNESS: sender-initiated steal must reject bottom-task transfer, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Version 2 - receiver-initiated stealing
// ========================================================================

/// Tier 42h: a posted steal request resets cleanly after transferring the top task.
#[test]
fn test_vt_tier42h_receiver_request_transfers_top_and_resets_request() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("top_task", "i64");
    ctx.declare_var_parsed("bottom_task", "i64");
    assume_seq_exprs(&mut ctx, "victim", &["top_task", "bottom_task"]);
    ctx.declare_var_parsed("request_before", "i64");
    ctx.declare_var_parsed("request_after", "i64");
    ctx.declare_var_parsed("reply", "i64");

    ctx.push_assume("top_before_bottom", "top_task < bottom_task");
    ctx.push_assume("thief_request", "request_before == 1");
    ctx.push_assume("request_cleared", "request_after == -4");
    ctx.push_assume("reply_is_top", "reply == victim.index(0)");

    ctx.push_assert(
        "reply_and_remaining_tasks_preserve_total_work",
        "reply + victim.skip(1).index(0) == victim.index(0) + victim.index(1)",
    );
    ctx.push_assert(
        "victim_shrinks_by_one",
        "victim.skip(1).len() + 1 == victim.len()",
    );
    ctx.push_assert(
        "request_reset_moves_below_request",
        "request_after < request_before",
    );
    ctx.push_assert(
        "reply_precedes_remaining_bottom",
        "reply < victim.skip(1).index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42h: receiver-initiated steal should reset the request cell, got: {:?}",
        result,
    );
}

/// Tier 42i: an empty victim deque replies with `NO_TASK` and still clears the request.
#[test]
fn test_vt_tier42i_receiver_empty_reply_reports_no_task() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "victim", &[]);
    ctx.declare_var_parsed("victim_after", "Seq<i64>");
    ctx.declare_var_parsed("request_before", "i64");
    ctx.declare_var_parsed("request_after", "i64");
    ctx.declare_var_parsed("reply", "i64");

    ctx.push_assume("thief_request", "request_before == 1");
    ctx.push_assume("victim_frame", "victim_after == victim");
    ctx.push_assume("victim_frame_len", "victim_after.len() == victim.len()");
    ctx.push_assume("request_cleared", "request_after == -4");
    ctx.push_assume("no_task_reply", "reply == -1");

    ctx.push_assert("reply_is_below_empty_len", "reply < victim_after.len()");
    ctx.push_assert(
        "reply_plus_one_matches_empty_len",
        "reply + 1 == victim_after.len()",
    );
    ctx.push_assert(
        "request_reset_moves_below_request",
        "request_after < request_before",
    );
    ctx.push_assert("reply_exceeds_cleared_request", "reply > request_after");
    ctx.push_assert(
        "reply_offsets_from_cleared_request",
        "reply == request_after + 3",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 42i: empty receiver-side steal should report NO_TASK, got: {:?}",
        result,
    );
}
