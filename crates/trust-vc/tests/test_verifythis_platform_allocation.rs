// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 73 - Sweep-Line Platform Allocation VCs.
//!
//! Sweep-line resource-allocation problems are common VerifyThis material:
//! sort arrivals and departures, scan the next event, and maintain the number
//! of currently occupied resources plus the peak seen so far.
//!
//! This tier uses closed-interval platform semantics: if an arrival occurs at
//! the exact time of a departure, the arrival is processed first and still
//! needs its own platform. That tie rule differs from Tier 72's half-open
//! room-reuse reasoning and exercises a distinct proof shape.
//!
//! Core proof obligations:
//!   1. Arrival and departure event streams are individually sorted.
//!   2. A new arrival before or at the next departure increases the active
//!      platform count by one.
//!   3. A departure after the peak releases one platform without underflow.
//!   4. Later arrivals can reuse freed capacity without changing the global
//!      peak once the high-water mark is established.
//!   5. Negatives: processing a tie as departure-first, decrementing from zero,
//!      or claiming a smaller peak are unsound.
//!
//! Example event streams:
//!   arrivals   = [1, 2, 4, 7]
//!   departures = [4, 5, 8, 9]
//!
//! Closed semantics yield the sweep trace:
//!   after 1a: 1
//!   after 2a: 2
//!   after 4a: 3   (tie with first departure, arrival processed first)
//!   after 4d: 2
//!   after 5d: 1
//!   after 7a: 2
//!   after 8d: 1
//!   after 9d: 0
//! Peak occupancy is 3.
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

fn assume_platform_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "arrivals", &[1, 2, 4, 7]);
    assume_seq_u64(ctx, "departures", &[4, 5, 8, 9]);
}

fn assume_sweep_trace(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "active", &[1, 2, 3, 2, 1, 2, 1, 0]);
    assume_seq_u64(ctx, "peak", &[1, 2, 3, 3, 3, 3, 3, 3]);
}

// ========================================================================
// GROUP A: Sorted event streams and initialization
// ========================================================================

/// Tier 73a: arrival/departure streams are individually sorted and well formed.
#[test]
fn test_vt_tier73a_event_streams_are_sorted() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);

    ctx.push_assert("a01", "arrivals.index(0) <= arrivals.index(1)");
    ctx.push_assert("a12", "arrivals.index(1) <= arrivals.index(2)");
    ctx.push_assert("a23", "arrivals.index(2) <= arrivals.index(3)");

    ctx.push_assert("d01", "departures.index(0) <= departures.index(1)");
    ctx.push_assert("d12", "departures.index(1) <= departures.index(2)");
    ctx.push_assert("d23", "departures.index(2) <= departures.index(3)");

    ctx.push_assert(
        "first_event_is_arrival",
        "arrivals.index(0) <= departures.index(0)",
    );
    ctx.push_assert(
        "last_departure_closes_schedule",
        "arrivals.index(3) <= departures.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73a: sorted sweep-line streams should verify, got: {:?}",
        result,
    );
}

/// Tier 73a: the first arrival seeds one active platform and peak one.
#[test]
fn test_vt_tier73a_first_arrival_seeds_active_count() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert(
        "first_arrival_before_first_departure",
        "arrivals.index(0) < departures.index(0)",
    );
    ctx.push_assert("nonzero_after_seed", "active.index(0) > 0");
    ctx.push_assert(
        "two_more_arrivals_raise_count_by_two",
        "active.index(2) == active.index(0) + 2",
    );
    ctx.push_assert(
        "peak_at_tie_is_two_higher_than_seed",
        "peak.index(2) == active.index(0) + 2",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73a: first arrival should seed one platform, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Arrival events grow the active count
// ========================================================================

/// Tier 73b: the second arrival precedes the first departure and raises occupancy to two.
#[test]
fn test_vt_tier73b_second_arrival_increments_active_count() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert(
        "arrival_before_departure",
        "arrivals.index(1) < departures.index(0)",
    );
    ctx.push_assert("active_grows", "active.index(1) > active.index(0)");
    ctx.push_assert("peak_grows", "peak.index(1) > peak.index(0)");
    ctx.push_assert(
        "future_peak_still_exceeds_second_arrival",
        "active.index(1) < peak.index(7)",
    );
    ctx.push_assert(
        "seed_plus_second_arrival_matches_peak_at_tie",
        "active.index(0) + active.index(1) == peak.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73b: early arrival should increase occupancy to two, got: {:?}",
        result,
    );
}

/// Tier 73b: a tie arrival at time 4 is processed before the departure and reaches the peak of three.
#[test]
fn test_vt_tier73b_tie_arrival_hits_peak_before_departure() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert("tie_time", "arrivals.index(2) == departures.index(0)");
    ctx.push_assert("tie_still_increments", "active.index(2) > active.index(1)");
    ctx.push_assert(
        "peak_equals_two_more_than_seed",
        "peak.index(2) == active.index(0) + 2",
    );
    ctx.push_assert(
        "tie_peak_exceeds_post_departure",
        "active.index(2) > active.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73b: tie arrival should hit the 3-platform peak, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Departures release platforms and preserve the peak
// ========================================================================

/// Tier 73c: the departure at time 4 releases one platform after the peak.
#[test]
fn test_vt_tier73c_departure_after_peak_decrements_without_underflow() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert("tie_departure_time", "departures.index(0) == 4");
    ctx.push_assert(
        "departure_releases_one",
        "active.index(3) < active.index(2)",
    );
    ctx.push_assert("still_positive", "active.index(3) >= 1");
    ctx.push_assert(
        "departure_restores_pre_tie_occupancy",
        "active.index(3) == active.index(1)",
    );
    ctx.push_assert(
        "peak_retained_above_live",
        "peak.index(3) > active.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73c: departure after the peak should release exactly one platform, got: {:?}",
        result,
    );
}

/// Tier 73c: after another departure, the late arrival at time 7 reuses capacity without raising the peak.
#[test]
fn test_vt_tier73c_late_arrival_reuses_capacity_below_peak() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert(
        "second_departure_before_late_arrival",
        "departures.index(1) < arrivals.index(3)",
    );
    ctx.push_assert(
        "second_departure_releases_one",
        "active.index(4) < active.index(3)",
    );
    ctx.push_assert(
        "late_arrival_reuses_capacity",
        "active.index(5) > active.index(4)",
    );
    ctx.push_assert(
        "late_arrival_sits_one_below_peak",
        "active.index(5) + 1 == peak.index(5)",
    );
    ctx.push_assert("late_arrival_below_peak", "active.index(5) < peak.index(5)");
    ctx.push_assert(
        "peak_stays_at_tie_high_water_mark",
        "peak.index(5) == peak.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73c: late arrival should stay below the established peak, got: {:?}",
        result,
    );
}

/// Tier 73c: the full sweep trace ends empty while preserving the global peak of three.
#[test]
fn test_vt_tier73c_full_trace_preserves_peak_and_ends_empty() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    ctx.push_assert("peak_at_end", "peak.index(7) == peak.index(2)");
    ctx.push_assert("ends_empty", "active.index(7) == 0");
    ctx.push_assert(
        "last_departure_releases_final_platform",
        "active.index(6) > active.index(7)",
    );
    ctx.push_assert(
        "final_peak_exceeds_last_live_occupancy",
        "peak.index(7) > active.index(6)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 73c: full platform-allocation trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 73d NEGATIVE: treating the time-4 tie as departure-first would leave
/// active[2] at 2 instead of 3.  The correct closed-interval sweep processes
/// the arrival first, reaching peak 3.  Asserting active[2]==2 against the
/// real trace must produce a counterexample.
#[test]
fn test_vt_tier73d_processing_tie_as_departure_first_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    // If the tie were processed departure-first, the count would stay at 2.
    // The correct trace has active[2]==3, so this claim is refuted.
    ctx.push_assert("wrong_tie_order", "active.index(2) == active.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 73d SOUNDNESS: tie-as-departure-first should be rejected, got: {:?}",
        result,
    );
}

/// Tier 73d NEGATIVE: after the schedule drains to zero (active[7]==0),
/// claiming a further departure could still succeed is unsound.  The Seq
/// trace proves occupancy is already empty.
#[test]
fn test_vt_tier73d_departure_from_zero_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    // active[7]==0 in the trace.  A departure from zero is impossible.
    ctx.push_assert("false_release_from_zero", "active.index(7) >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 73d SOUNDNESS: departing from zero occupancy should be rejected, got: {:?}",
        result,
    );
}

/// Tier 73d NEGATIVE: the schedule requires 3 platforms (peak[7]==3), so
/// claiming that 2 platforms suffice must be rejected.  Uses the Seq trace
/// to derive the peak from the sweep data rather than a disconnected scalar.
#[test]
fn test_vt_tier73d_claiming_peak_two_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_platform_example(&mut ctx);
    assume_sweep_trace(&mut ctx);

    // peak[7]==3 in the trace.  Two platforms cannot service this schedule.
    ctx.push_assert("false_peak_bound", "peak.index(7) <= 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 73d SOUNDNESS: three-platform peak should not fit in two, got: {:?}",
        result,
    );
}
