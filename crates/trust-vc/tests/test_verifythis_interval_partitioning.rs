// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 72 - Interval Partitioning / Minimum Rooms VCs.
//!
//! Interval partitioning is the room-allocation companion to interval
//! scheduling: process intervals in start-time order and reuse the room whose
//! meeting finishes earliest when possible; otherwise allocate a new room.
//!
//! Core proof obligations:
//!   1. Inputs are valid intervals sorted by start time.
//!   2. An overlapping interval opens a fresh room and increases the room count.
//!   3. A compatible interval reuses the earliest-finishing room without
//!      increasing the room count.
//!   4. The room-end priority queue remains sorted after each step.
//!   5. Negatives: reusing an overlapping room, undercounting the peak, or
//!      forgetting to retire the earliest end are unsound.
//!
//! We use the standard "meeting rooms" example:
//!   [0,3], [1,4], [2,5], [4,6], [6,8]
//! The peak overlap is 3, so the optimal partition uses 3 rooms.
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

fn assume_seq_u64_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    ctx.declare_var_parsed(name, "Seq<u64>");
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

fn assume_interval_partitioning_example(ctx: &mut VerificationContext) {
    // Sorted by start time:
    //   0: [0,3]   1: [1,4]   2: [2,5]   3: [4,6]   4: [6,8]
    // Greedy room-end traces:
    //   after 0: [3]
    //   after 1: [3,4]
    //   after 2: [3,4,5]
    //   after 3: [4,5,6]
    //   after 4: [5,6,8]
    assume_seq_u64(ctx, "starts", &[0, 1, 2, 4, 6]);
    assume_seq_u64(ctx, "finishes", &[3, 4, 5, 6, 8]);
}

fn assume_room_trace(ctx: &mut VerificationContext) {
    assume_seq_u64_exprs(ctx, "room_ends_0", &["finishes.index(0)"]);
    assume_seq_u64_exprs(
        ctx,
        "room_ends_1",
        &["room_ends_0.index(0)", "finishes.index(1)"],
    );
    assume_seq_u64_exprs(
        ctx,
        "room_ends_2",
        &[
            "room_ends_1.index(0)",
            "room_ends_1.index(1)",
            "finishes.index(2)",
        ],
    );
    assume_seq_u64_exprs(
        ctx,
        "room_ends_3",
        &[
            "room_ends_2.index(1)",
            "room_ends_2.index(2)",
            "finishes.index(3)",
        ],
    );
    assume_seq_u64_exprs(
        ctx,
        "room_ends_4",
        &[
            "room_ends_3.index(1)",
            "room_ends_3.index(2)",
            "finishes.index(4)",
        ],
    );
}

// ========================================================================
// GROUP A: Input ordering and first room allocation
// ========================================================================

/// Tier 72a: example intervals are sorted by start time and individually valid.
#[test]
fn test_vt_tier72a_intervals_sorted_and_valid() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);

    ctx.push_assert("s01", "starts.index(0) <= starts.index(1)");
    ctx.push_assert("s12", "starts.index(1) <= starts.index(2)");
    ctx.push_assert("s23", "starts.index(2) <= starts.index(3)");
    ctx.push_assert("s34", "starts.index(3) <= starts.index(4)");

    ctx.push_assert("i0_valid", "starts.index(0) < finishes.index(0)");
    ctx.push_assert("i1_valid", "starts.index(1) < finishes.index(1)");
    ctx.push_assert("i2_valid", "starts.index(2) < finishes.index(2)");
    ctx.push_assert("i3_valid", "starts.index(3) < finishes.index(3)");
    ctx.push_assert("i4_valid", "starts.index(4) < finishes.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72a: sorted valid intervals should verify, got: {:?}",
        result,
    );
}

/// Tier 72a: the first interval opens one room whose end equals its finish.
#[test]
fn test_vt_tier72a_first_interval_opens_one_room() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert("single_room", "room_ends_0.len() == 1");
    ctx.push_assert(
        "end_matches_first_finish",
        "room_ends_0.index(0) == finishes.index(0)",
    );
    ctx.push_assert(
        "first_interval_starts_before_end",
        "starts.index(0) < room_ends_0.index(0)",
    );
    ctx.push_assert(
        "first_room_finish_bounds_rest",
        "room_ends_0.index(0) <= finishes.index(2) + finishes.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72a: first room allocation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Overlap opens fresh rooms
// ========================================================================

/// Tier 72b: interval [1,4] overlaps [0,3], so the room count increases to 2.
#[test]
fn test_vt_tier72b_overlap_opens_second_room() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert(
        "overlaps_first_room",
        "starts.index(1) < room_ends_0.index(0)",
    );
    ctx.push_assert("count_grows", "room_ends_1.len() == room_ends_0.len() + 1");
    ctx.push_assert(
        "sorted_after_insert",
        "room_ends_1.index(0) <= room_ends_1.index(1)",
    );
    ctx.push_assert(
        "new_room_tracks_finish",
        "room_ends_1.index(1) == finishes.index(1)",
    );
    ctx.push_assert(
        "old_room_preserved",
        "room_ends_1.index(0) == room_ends_0.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72b: first overlap should open a second room, got: {:?}",
        result,
    );
}

/// Tier 72b: interval [2,5] also overlaps the earliest end, forcing a third room.
#[test]
fn test_vt_tier72b_peak_overlap_opens_third_room() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert(
        "overlaps_earliest_end",
        "starts.index(2) < room_ends_1.index(0)",
    );
    ctx.push_assert(
        "count_grows_again",
        "room_ends_2.len() == room_ends_1.len() + 1",
    );
    ctx.push_assert("sorted_01", "room_ends_2.index(0) <= room_ends_2.index(1)");
    ctx.push_assert("sorted_12", "room_ends_2.index(1) <= room_ends_2.index(2)");
    ctx.push_assert(
        "third_room_tracks_finish",
        "room_ends_2.index(2) == finishes.index(2)",
    );
    ctx.push_assert(
        "sum_matches_first_three_finishes",
        "room_ends_2.index(0) + room_ends_2.index(1) + room_ends_2.index(2) == finishes.index(0) + finishes.index(1) + finishes.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72b: peak overlap should open a third room, got: {:?}",
        result,
    );
}

/// Tier 72b: at time 2 all first three intervals are active, witnessing the peak of 3 rooms.
#[test]
fn test_vt_tier72b_time_two_witnesses_three_active_intervals() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);
    ctx.declare_var_parsed("time", "u64");
    ctx.push_assume("time_2", "time == 2");

    ctx.push_assert("i0_started", "starts.index(0) <= time");
    ctx.push_assert("i0_not_finished", "time < finishes.index(0)");
    ctx.push_assert("i1_started", "starts.index(1) <= time");
    ctx.push_assert("i1_not_finished", "time < finishes.index(1)");
    ctx.push_assert("i2_started", "starts.index(2) <= time");
    ctx.push_assert("i2_not_finished", "time < finishes.index(2)");
    ctx.push_assert("three_rooms_live", "room_ends_2.len() == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72b: time-2 overlap witness should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Compatible intervals reuse the earliest room
// ========================================================================

/// Tier 72c: interval [4,6] reuses the room ending at 3, so the room count stays flat.
#[test]
fn test_vt_tier72c_reuse_earliest_room_without_growth() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert("compatible", "starts.index(3) >= room_ends_2.index(0)");
    ctx.push_assert("count_flat", "room_ends_3.len() == room_ends_2.len()");
    ctx.push_assert(
        "retire_old_min",
        "room_ends_3.index(0) == room_ends_2.index(1)",
    );
    ctx.push_assert(
        "new_finish_inserted",
        "room_ends_3.index(2) == finishes.index(3)",
    );
    ctx.push_assert("sorted_01", "room_ends_3.index(0) <= room_ends_3.index(1)");
    ctx.push_assert("sorted_12", "room_ends_3.index(1) <= room_ends_3.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72c: compatible interval should reuse earliest room, got: {:?}",
        result,
    );
}

/// Tier 72c: interval [6,8] reuses the next earliest room and still needs only 3 rooms.
#[test]
fn test_vt_tier72c_second_reuse_keeps_three_room_budget() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert(
        "compatible_again",
        "starts.index(4) >= room_ends_3.index(0)",
    );
    ctx.push_assert("still_three_rooms", "room_ends_4.len() == 3");
    ctx.push_assert(
        "retire_second_min",
        "room_ends_4.index(0) == room_ends_3.index(1)",
    );
    ctx.push_assert(
        "new_last_finish",
        "room_ends_4.index(2) == finishes.index(4)",
    );
    ctx.push_assert("sorted_01", "room_ends_4.index(0) <= room_ends_4.index(1)");
    ctx.push_assert("sorted_12", "room_ends_4.index(1) <= room_ends_4.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72c: second reuse should keep the 3-room budget, got: {:?}",
        result,
    );
}

/// Tier 72c: the full greedy trace peaks at 3 rooms and ends with latest finish 8.
#[test]
fn test_vt_tier72c_full_trace_uses_three_rooms() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);
    ctx.declare_var_parsed("peak_rooms", "u64");
    ctx.push_assume("peak_rooms_3", "peak_rooms == 3");

    ctx.push_assert(
        "peak_after_third_interval",
        "room_ends_2.len() == peak_rooms",
    );
    ctx.push_assert("reuse_keeps_peak", "room_ends_3.len() == peak_rooms");
    ctx.push_assert("final_room_count", "room_ends_4.len() == peak_rooms");
    ctx.push_assert(
        "latest_finish_preserved",
        "room_ends_4.index(2) == finishes.index(4)",
    );
    ctx.push_assert(
        "final_sum_matches_live_rooms",
        "room_ends_4.index(0) + room_ends_4.index(1) + room_ends_4.index(2) == finishes.index(2) + finishes.index(3) + finishes.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 72c: full interval-partitioning trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 72d NEGATIVE: reusing the first room for [1,4] is unsound because it still overlaps [0,3].
#[test]
fn test_vt_tier72d_reusing_overlapping_room_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert(
        "false_compatibility",
        "starts.index(1) >= room_ends_0.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 72d SOUNDNESS: overlapping room reuse should be rejected, got: {:?}",
        result,
    );
}

/// Tier 72d NEGATIVE: claiming the peak overlap fits in only two rooms is unsound.
#[test]
fn test_vt_tier72d_claiming_two_rooms_for_peak_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert("false_peak_bound", "room_ends_2.len() == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 72d SOUNDNESS: peak overlap should not fit in two rooms, got: {:?}",
        result,
    );
}

/// Tier 72d NEGATIVE: after reusing a room, the old minimum end cannot remain at the front.
#[test]
fn test_vt_tier72d_failing_to_retire_old_minimum_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_interval_partitioning_example(&mut ctx);
    assume_room_trace(&mut ctx);

    ctx.push_assert(
        "stale_minimum",
        "room_ends_3.index(0) == room_ends_2.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 72d SOUNDNESS: stale earliest end should be rejected, got: {:?}",
        result,
    );
}
