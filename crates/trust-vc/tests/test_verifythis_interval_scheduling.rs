// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 68 — Interval Scheduling / Activity Selection VCs.
//!
//! Interval scheduling is a classic VerifyThis-style greedy problem: given
//! intervals sorted by finish time, repeatedly pick the next interval whose
//! start is at least the finish of the last chosen one.
//!
//! Core proof obligations:
//!   1. Init: the first chosen interval has the earliest finish time
//!   2. Step: compatible intervals increment the count and advance `last_finish`
//!   3. Exchange lemma: finishing earlier never reduces future compatibility
//!   4. Exit: a concrete scan yields the expected maximal compatible set
//!   5. Negatives: accepting overlap or preferring a later finish is unsound
//!
//! KEY LESSON: the greedy argument reduces to a small arithmetic fact:
//! `earlier_finish <= later_finish && next_start >= later_finish
//!  ==> next_start >= earlier_finish`.
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

fn assume_activity_selection_example(ctx: &mut VerificationContext) {
    // Sorted by finish time:
    //   0: [1,4]   1: [3,5]   2: [0,6]   3: [5,7]
    //   4: [8,9]   5: [5,9]   6: [9,11]
    // Greedy picks indices [0, 3, 4, 6].
    assume_seq_u64(ctx, "starts", &[1, 3, 0, 5, 8, 5, 9]);
    assume_seq_u64(ctx, "finishes", &[4, 5, 6, 7, 9, 9, 11]);
}

fn assume_full_scan_trace(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("count0", "u64");
    ctx.declare_var_parsed("count1", "u64");
    ctx.declare_var_parsed("count2", "u64");
    ctx.declare_var_parsed("count3", "u64");
    ctx.declare_var_parsed("count4", "u64");
    ctx.declare_var_parsed("count5", "u64");
    ctx.declare_var_parsed("count6", "u64");
    ctx.declare_var_parsed("last0", "u64");
    ctx.declare_var_parsed("last1", "u64");
    ctx.declare_var_parsed("last2", "u64");
    ctx.declare_var_parsed("last3", "u64");
    ctx.declare_var_parsed("last4", "u64");
    ctx.declare_var_parsed("last5", "u64");
    ctx.declare_var_parsed("last6", "u64");

    // Select 0 -> reject 1,2 -> select 3 -> select 4 -> reject 5 -> select 6
    ctx.push_assume("count0_1", "count0 == 1");
    ctx.push_assume("last0_4", "last0 == 4");
    ctx.push_assume("count1_1", "count1 == count0");
    ctx.push_assume("last1_4", "last1 == last0");
    ctx.push_assume("count2_1", "count2 == count1");
    ctx.push_assume("last2_4", "last2 == last1");
    ctx.push_assume("count3_2", "count3 == count2 + 1");
    ctx.push_assume("last3_7", "last3 == 7");
    ctx.push_assume("count4_3", "count4 == count3 + 1");
    ctx.push_assume("last4_9", "last4 == 9");
    ctx.push_assume("count5_3", "count5 == count4");
    ctx.push_assume("last5_9", "last5 == last4");
    ctx.push_assume("count6_4", "count6 == count5 + 1");
    ctx.push_assume("last6_11", "last6 == 11");
}

// ========================================================================
// GROUP A: Init — finish ordering and first choice
// ========================================================================

/// Tier 68a: the example intervals are sorted by finish time and individually valid.
#[test]
fn test_vt_tier68a_intervals_sorted_and_valid() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);

    ctx.push_assert("f01", "finishes.index(0) <= finishes.index(1)");
    ctx.push_assert("f12", "finishes.index(1) <= finishes.index(2)");
    ctx.push_assert("f23", "finishes.index(2) <= finishes.index(3)");
    ctx.push_assert("f34", "finishes.index(3) <= finishes.index(4)");
    ctx.push_assert("f45", "finishes.index(4) <= finishes.index(5)");
    ctx.push_assert("f56", "finishes.index(5) <= finishes.index(6)");

    ctx.push_assert("i0_valid", "starts.index(0) < finishes.index(0)");
    ctx.push_assert("i3_valid", "starts.index(3) < finishes.index(3)");
    ctx.push_assert("i4_valid", "starts.index(4) < finishes.index(4)");
    ctx.push_assert("i6_valid", "starts.index(6) < finishes.index(6)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68a: finish ordering should verify, got: {:?}",
        result,
    );
}

/// Tier 68a: picking the first interval records the earliest finish time.
#[test]
fn test_vt_tier68a_first_choice_uses_earliest_finish() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);
    ctx.declare_var_parsed("chosen", "u64");
    ctx.declare_var_parsed("last_finish", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("chosen_0", "chosen == 0");
    ctx.push_assume("last_finish_4", "last_finish == 4");
    ctx.push_assume("count_1", "count == 1");

    ctx.push_assert("chosen_finish", "finishes.index(chosen) == last_finish");
    ctx.push_assert("earlier_than_1", "last_finish <= finishes.index(1)");
    ctx.push_assert("earlier_than_2", "last_finish <= finishes.index(2)");
    ctx.push_assert("chosen_is_valid", "starts.index(chosen) < last_finish");
    ctx.push_assert("count_initialized", "count >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68a: first greedy choice should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — accept compatible interval, reject overlap
// ========================================================================

/// Tier 68b: after choosing [1,4], interval [5,7] is compatible and accepted.
#[test]
fn test_vt_tier68b_accept_compatible_interval() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");
    ctx.declare_var_parsed("last_finish", "u64");
    ctx.declare_var_parsed("last_finish_next", "u64");
    ctx.declare_var_parsed("idx", "u64");

    ctx.push_assume("count_1", "count == 1");
    ctx.push_assume("count_next_2", "count_next == 2");
    ctx.push_assume("last_finish_4", "last_finish == 4");
    ctx.push_assume("idx_3", "idx == 3");
    ctx.push_assume("last_finish_next_7", "last_finish_next == 7");

    ctx.push_assert("compatible", "starts.index(idx) >= last_finish");
    ctx.push_assert("advance_finish", "last_finish_next == finishes.index(idx)");
    ctx.push_assert("count_inc", "count_next == count + 1");
    ctx.push_assert("finish_monotone", "last_finish_next > last_finish");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68b: accepting a compatible interval should verify, got: {:?}",
        result,
    );
}

/// Tier 68b: after choosing [1,4], interval [3,5] overlaps and is rejected.
#[test]
fn test_vt_tier68b_reject_overlapping_interval() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");
    ctx.declare_var_parsed("last_finish", "u64");
    ctx.declare_var_parsed("last_finish_next", "u64");
    ctx.declare_var_parsed("idx", "u64");

    ctx.push_assume("count_1", "count == 1");
    ctx.push_assume("count_next_1", "count_next == 1");
    ctx.push_assume("last_finish_4", "last_finish == 4");
    ctx.push_assume("last_finish_next_4", "last_finish_next == 4");
    ctx.push_assume("idx_1", "idx == 1");

    ctx.push_assert("overlap", "starts.index(idx) < last_finish");
    ctx.push_assert("count_unchanged", "count_next == count");
    ctx.push_assert("finish_unchanged", "last_finish_next == last_finish");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68b: rejecting an overlapping interval should verify, got: {:?}",
        result,
    );
}

/// Tier 68b: after choosing [5,7] and [8,9], interval [5,9] still overlaps and is skipped.
#[test]
fn test_vt_tier68b_skip_late_overlapping_interval() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");
    ctx.declare_var_parsed("last_finish", "u64");
    ctx.declare_var_parsed("last_finish_next", "u64");
    ctx.declare_var_parsed("idx", "u64");

    ctx.push_assume("count_3", "count == 3");
    ctx.push_assume("count_next_3", "count_next == 3");
    ctx.push_assume("last_finish_9", "last_finish == 9");
    ctx.push_assume("last_finish_next_9", "last_finish_next == 9");
    ctx.push_assume("idx_5", "idx == 5");

    ctx.push_assert("still_overlaps", "starts.index(idx) < last_finish");
    ctx.push_assert("skip_count", "count_next == count");
    ctx.push_assert("skip_finish", "last_finish_next == last_finish");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68b: later overlapping interval should still be skipped, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariants — exchange lemma and selected-chain compatibility
// ========================================================================

/// Tier 68c: exchange lemma — finishing earlier preserves future compatibility.
#[test]
fn test_vt_tier68c_exchange_lemma() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("earlier_finish", "u64");
    ctx.declare_var_parsed("later_finish", "u64");
    ctx.declare_var_parsed("next_start", "u64");

    ctx.push_assume("bounded_earlier", "earlier_finish <= 1000");
    ctx.push_assume("bounded_later", "later_finish <= 1000");
    ctx.push_assume("bounded_next", "next_start <= 1000");
    ctx.push_assume("earlier_le_later", "earlier_finish <= later_finish");
    ctx.push_assume("compatible_with_later", "next_start >= later_finish");

    ctx.push_assert("compatible_with_earlier", "next_start >= earlier_finish");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68c: exchange lemma should verify, got: {:?}",
        result,
    );
}

/// Tier 68c: the selected greedy chain [0,3,4,6] is pairwise non-overlapping.
#[test]
fn test_vt_tier68c_selected_chain_is_nonoverlapping() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);

    ctx.push_assert("03_compatible", "finishes.index(0) <= starts.index(3)");
    ctx.push_assert("34_compatible", "finishes.index(3) <= starts.index(4)");
    ctx.push_assert("46_compatible", "finishes.index(4) <= starts.index(6)");

    ctx.push_assert(
        "finish_increase_03",
        "finishes.index(0) < finishes.index(3)",
    );
    ctx.push_assert(
        "finish_increase_34",
        "finishes.index(3) < finishes.index(4)",
    );
    ctx.push_assert(
        "finish_increase_46",
        "finishes.index(4) < finishes.index(6)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68c: chosen chain should be non-overlapping, got: {:?}",
        result,
    );
}

/// Tier 68c: choosing interval [5,7] leaves room for [8,9], but [5,9] would not.
#[test]
fn test_vt_tier68c_earlier_finish_leaves_more_room() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);

    ctx.push_assert("room_after_3", "starts.index(4) >= finishes.index(3)");
    ctx.push_assert("no_room_after_5", "starts.index(4) < finishes.index(5)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68c: earlier finish should leave more room, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Full scan and soundness negatives
// ========================================================================

/// Tier 68d: full greedy scan on the example selects four compatible intervals.
#[test]
fn test_vt_tier68d_full_scan_count_four() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);
    assume_full_scan_trace(&mut ctx);

    ctx.push_assert("reject_1", "starts.index(1) < last0");
    ctx.push_assert("reject_2", "starts.index(2) < last1");
    ctx.push_assert("accept_3", "starts.index(3) >= last2");
    ctx.push_assert("accept_4", "starts.index(4) >= last3");
    ctx.push_assert("reject_5", "starts.index(5) < last4");
    ctx.push_assert("accept_6", "starts.index(6) >= last5");

    ctx.push_assert("final_count", "count6 == 4");
    ctx.push_assert("final_finish", "last6 == finishes.index(6)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 68d: full interval-scheduling scan should verify, got: {:?}",
        result,
    );
}

/// Tier 68d NEGATIVE: claiming [1,4] and [3,5] are compatible is unsound.
#[test]
fn test_vt_tier68d_negative_accept_overlap() {
    let mut ctx = VerificationContext::new();
    assume_activity_selection_example(&mut ctx);

    ctx.push_assert("wrong_nonoverlap", "finishes.index(0) <= starts.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 68d SOUNDNESS: overlapping intervals should be rejected, got: {:?}",
        result,
    );
}

/// Tier 68d NEGATIVE: compatibility with an earlier finish does not imply
/// compatibility with a later finish.
#[test]
fn test_vt_tier68d_negative_later_finish_preserves_room() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("earlier_finish", "u64");
    ctx.declare_var_parsed("later_finish", "u64");
    ctx.declare_var_parsed("next_start", "u64");

    ctx.push_assume("earlier_7", "earlier_finish == 7");
    ctx.push_assume("later_9", "later_finish == 9");
    ctx.push_assume("next_8", "next_start == 8");
    ctx.push_assume("ordered", "earlier_finish < later_finish");
    ctx.push_assume("fits_earlier", "next_start >= earlier_finish");

    ctx.push_assert("wrong_fits_later", "next_start >= later_finish");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 68d SOUNDNESS: later finish should reduce future room, got: {:?}",
        result,
    );
}
