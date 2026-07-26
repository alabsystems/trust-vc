// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 80 - Open Addressing / Linear Probing Hash Table VCs.
//!
//! Sequential open-addressing tables are a recurring VerifyThis pattern:
//!   1. probe indices advance by one with modular wrap-around
//!   2. a contiguous live/tombstone cluster continues until the first empty slot
//!   3. lookup must skip live mismatches and tombstones until it finds a match
//!      or the first empty slot
//!   4. insertion uses the earliest empty or tombstone bucket in the probe chain
//!   5. deletion must leave TOMBSTONE rather than EMPTY when later wrapped keys
//!      still depend on the cluster
//!
//! Concrete 4-slot wrapped cluster used below:
//!   state = [LIVE, EMPTY, LIVE, LIVE]
//!   keys  = [target,  -,     home, probe]
//!   home = 2, probe1 = 3, probe2 = 0, probe3 = 1
//!
//! State encoding:
//!   0 = EMPTY
//!   1 = LIVE
//!   2 = TOMBSTONE
//!
//! 10 tests: 7 positive (probe wrap, cluster shape, lookup, insert, tombstone
//! reuse, delete) + 3 negatives.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

#[path = "support/verifythis_open_addressing_hash_table.rs"]
mod verifythis_open_addressing_hash_table_support;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;
use verifythis_open_addressing_hash_table_support::{
    assume_distinct_i64, assume_non_sentinel_i64, assume_seq_exprs, assume_seq_i64,
    assume_wrap_probe_indices, verify_with_pipeline,
};

fn assume_wrapped_cluster(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state", &[1, 0, 1, 1]);
    assume_seq_exprs(ctx, "slot_key", &["target", "-1", "home_key", "probe_key"]);

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "probe_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "probe_key");
    assume_distinct_i64(ctx, "home_key", "target");
    assume_distinct_i64(ctx, "probe_key", "target");
}

fn assume_wrap_insert_trace(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state_before", &[0, 0, 1, 1]);
    assume_seq_i64(ctx, "slot_state_after", &[1, 0, 1, 1]);
    assume_seq_exprs(
        ctx,
        "slot_key_before",
        &["-1", "-1", "home_key", "probe_key"],
    );
    assume_seq_exprs(
        ctx,
        "slot_key_after",
        &["target", "-1", "home_key", "probe_key"],
    );

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "probe_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "probe_key");
    assume_distinct_i64(ctx, "home_key", "target");
    assume_distinct_i64(ctx, "probe_key", "target");
}

fn assume_wrap_tombstone_reuse_trace(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("stale_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state_before", &[2, 0, 1, 1]);
    assume_seq_i64(ctx, "slot_state_after", &[1, 0, 1, 1]);
    assume_seq_exprs(
        ctx,
        "slot_key_before",
        &["stale_key", "-1", "home_key", "probe_key"],
    );
    assume_seq_exprs(
        ctx,
        "slot_key_after",
        &["target", "-1", "home_key", "probe_key"],
    );

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "probe_key");
    assume_non_sentinel_i64(ctx, "stale_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "probe_key");
    assume_distinct_i64(ctx, "home_key", "stale_key");
    assume_distinct_i64(ctx, "home_key", "target");
    assume_distinct_i64(ctx, "probe_key", "stale_key");
    assume_distinct_i64(ctx, "probe_key", "target");
    assume_distinct_i64(ctx, "stale_key", "target");
}

fn assume_wrap_delete_trace(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state_before", &[1, 0, 1, 1]);
    assume_seq_i64(ctx, "slot_state_after", &[1, 0, 1, 2]);
    assume_seq_exprs(
        ctx,
        "slot_key_before",
        &["target", "-1", "home_key", "probe_key"],
    );
    assume_seq_exprs(
        ctx,
        "slot_key_after",
        &["target", "-1", "home_key", "probe_key"],
    );

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "probe_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "probe_key");
    assume_distinct_i64(ctx, "home_key", "target");
    assume_distinct_i64(ctx, "probe_key", "target");
}

fn assume_broken_gap_cluster(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state", &[1, 0, 1, 0]);
    assume_seq_exprs(ctx, "slot_key", &["target", "-1", "home_key", "-1"]);

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "target");
}

fn assume_skip_earliest_empty_trace(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("target", "i64");

    assume_wrap_probe_indices(ctx);
    assume_seq_i64(ctx, "slot_state_before", &[0, 0, 1, 1]);
    assume_seq_i64(ctx, "slot_state_after", &[0, 1, 1, 1]);
    assume_seq_exprs(
        ctx,
        "slot_key_before",
        &["-1", "-1", "home_key", "probe_key"],
    );
    assume_seq_exprs(
        ctx,
        "slot_key_after",
        &["-1", "target", "home_key", "probe_key"],
    );

    assume_non_sentinel_i64(ctx, "home_key");
    assume_non_sentinel_i64(ctx, "probe_key");
    assume_non_sentinel_i64(ctx, "target");
    assume_distinct_i64(ctx, "home_key", "probe_key");
    assume_distinct_i64(ctx, "home_key", "target");
    assume_distinct_i64(ctx, "probe_key", "target");
}

// ========================================================================
// GROUP A: Probe wrap-around and cluster shape
// ========================================================================

/// Tier 80a: the probe chain wraps from slot 3 back to slot 0 and stays in bounds.
#[test]
fn test_vt_tier80a_probe_chain_wraps_and_stays_in_bounds() {
    let mut ctx = VerificationContext::new();
    assume_wrap_probe_indices(&mut ctx);

    ctx.push_assert("probe1_is_three", "probe1 == 3");
    ctx.push_assert("probe2_wraps_to_zero", "probe2 == 0");
    ctx.push_assert("probe3_advances_to_one", "probe3 == 1");
    ctx.push_assert("home_in_bounds", "home < n");
    ctx.push_assert("probe1_in_bounds", "probe1 < n");
    ctx.push_assert("probe2_in_bounds", "probe2 < n");
    ctx.push_assert("probe3_in_bounds", "probe3 < n");
    ctx.push_assert("wrapped_probe_differs_from_tail", "probe2 != probe1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80a: wrapped probe chain should verify, got: {:?}",
        result,
    );
}

/// Tier 80a: the wrapped cluster occupies home, probe1, and probe2 before the first empty probe3.
#[test]
fn test_vt_tier80a_wrapped_cluster_stays_contiguous_until_first_empty() {
    let mut ctx = VerificationContext::new();
    assume_wrapped_cluster(&mut ctx);

    ctx.push_assert("home_live", "slot_state.index(home) == 1");
    ctx.push_assert("probe1_live", "slot_state.index(probe1) == 1");
    ctx.push_assert("probe2_live", "slot_state.index(probe2) == 1");
    ctx.push_assert("probe3_empty", "slot_state.index(probe3) == 0");
    ctx.push_assert("home_keeps_home_key", "slot_key.index(home) == home_key");
    ctx.push_assert(
        "probe1_keeps_probe_key",
        "slot_key.index(probe1) == probe_key",
    );
    ctx.push_assert("probe2_keeps_target", "slot_key.index(probe2) == target");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80a: wrapped cluster shape should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Lookup, insertion, and tombstones
// ========================================================================

/// Tier 80b: wrapped lookup skips two live mismatches before reaching the target at probe2.
#[test]
fn test_vt_tier80b_wrapped_lookup_reaches_target_after_two_collisions() {
    let mut ctx = VerificationContext::new();
    assume_wrapped_cluster(&mut ctx);

    ctx.push_assert(
        "home_is_live_mismatch",
        "slot_state.index(home) == 1 && slot_key.index(home) != target",
    );
    ctx.push_assert(
        "probe1_is_live_mismatch",
        "slot_state.index(probe1) == 1 && slot_key.index(probe1) != target",
    );
    ctx.push_assert(
        "probe2_is_target_bucket",
        "slot_state.index(probe2) == 1 && slot_key.index(probe2) == target",
    );
    ctx.push_assert(
        "search_has_not_terminated_early",
        "slot_state.index(probe3) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80b: wrapped lookup should reach the target bucket, got: {:?}",
        result,
    );
}

/// Tier 80b: insertion after two collisions uses the wrapped empty bucket at probe2.
#[test]
fn test_vt_tier80b_wrap_insert_uses_first_empty_bucket() {
    let mut ctx = VerificationContext::new();
    assume_wrap_insert_trace(&mut ctx);

    ctx.push_assert("home_live_before", "slot_state_before.index(home) == 1");
    ctx.push_assert("probe1_live_before", "slot_state_before.index(probe1) == 1");
    ctx.push_assert(
        "probe2_empty_before",
        "slot_state_before.index(probe2) == 0",
    );
    ctx.push_assert("probe2_live_after", "slot_state_after.index(probe2) == 1");
    ctx.push_assert(
        "wrapped_bucket_gets_target",
        "slot_key_after.index(probe2) == target",
    );
    ctx.push_assert(
        "home_key_preserved",
        "slot_key_after.index(home) == home_key",
    );
    ctx.push_assert(
        "probe1_key_preserved",
        "slot_key_after.index(probe1) == probe_key",
    );
    ctx.push_assert(
        "later_empty_stays_empty",
        "slot_state_after.index(probe3) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80b: wrapped insert should use the earliest empty bucket, got: {:?}",
        result,
    );
}

/// Tier 80b: wrapped insertion increases the live-slot count by exactly one.
#[test]
fn test_vt_tier80b_wrap_insert_increases_live_count_by_one() {
    let mut ctx = VerificationContext::new();
    assume_wrap_insert_trace(&mut ctx);

    ctx.push_assert(
        "live_count_delta",
        "slot_state_after.index(home) + slot_state_after.index(probe1) + \
         slot_state_after.index(probe2) == \
         slot_state_before.index(home) + slot_state_before.index(probe1) + \
         slot_state_before.index(probe2) + 1",
    );
    ctx.push_assert("probe3_stays_empty", "slot_state_after.index(probe3) == 0");
    ctx.push_assert(
        "wrapped_target_visible",
        "slot_key_after.index(probe2) == target",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80b: wrapped insert should raise the live count by one, got: {:?}",
        result,
    );
}

/// Tier 80b: insertion reuses a wrapped tombstone before probing to a later empty bucket.
#[test]
fn test_vt_tier80b_tombstone_reuse_happens_before_later_empty() {
    let mut ctx = VerificationContext::new();
    assume_wrap_tombstone_reuse_trace(&mut ctx);

    ctx.push_assert(
        "wrapped_bucket_was_tombstone",
        "slot_state_before.index(probe2) == 2",
    );
    ctx.push_assert(
        "wrapped_bucket_live_after",
        "slot_state_after.index(probe2) == 1",
    );
    ctx.push_assert(
        "wrapped_bucket_gets_target",
        "slot_key_after.index(probe2) == target",
    );
    ctx.push_assert(
        "stale_payload_replaced",
        "slot_key_before.index(probe2) != slot_key_after.index(probe2)",
    );
    ctx.push_assert(
        "home_key_preserved",
        "slot_key_after.index(home) == home_key",
    );
    ctx.push_assert(
        "probe1_key_preserved",
        "slot_key_after.index(probe1) == probe_key",
    );
    ctx.push_assert(
        "later_empty_stays_empty",
        "slot_state_after.index(probe3) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80b: wrapped tombstone reuse should verify, got: {:?}",
        result,
    );
}

/// Tier 80b: deleting the tail collision leaves a tombstone so wrapped lookup can still reach the target.
#[test]
fn test_vt_tier80b_delete_marks_tombstone_and_preserves_wrapped_target() {
    let mut ctx = VerificationContext::new();
    assume_wrap_delete_trace(&mut ctx);

    ctx.push_assert("home_stays_live", "slot_state_after.index(home) == 1");
    ctx.push_assert(
        "deleted_bucket_is_tombstone",
        "slot_state_after.index(probe1) == 2",
    );
    ctx.push_assert(
        "deleted_bucket_not_empty",
        "slot_state_after.index(probe1) != 0",
    );
    ctx.push_assert(
        "wrapped_target_still_live",
        "slot_state_after.index(probe2) == 1",
    );
    ctx.push_assert(
        "wrapped_target_still_visible",
        "slot_key_after.index(probe2) == target",
    );
    ctx.push_assert(
        "later_empty_stays_empty",
        "slot_state_after.index(probe3) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 80b: delete-to-tombstone should preserve wrapped lookup, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 80c NEGATIVE: a live mismatch at home must not justify stopping before a later wrapped target.
#[test]
fn test_vt_tier80c_live_mismatch_must_not_terminate_lookup() {
    let mut ctx = VerificationContext::new();
    assume_wrapped_cluster(&mut ctx);

    ctx.push_assert(
        "wrong_stop_after_home_mismatch",
        "!(slot_state.index(home) == 1 && slot_key.index(home) != target) || \
         slot_state.index(probe2) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 80c NEGATIVE: live-mismatch early stop should be rejected, got: {:?}",
        result,
    );
}

/// Tier 80c NEGATIVE: an empty gap cannot appear before a later wrapped live target in the same probe chain.
#[test]
fn test_vt_tier80c_empty_gap_before_wrapped_target_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_broken_gap_cluster(&mut ctx);

    ctx.push_assert(
        "wrong_gap_before_later_target",
        "!(slot_state.index(probe1) == 0) || slot_state.index(probe2) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 80c NEGATIVE: empty gap before later target should be rejected, got: {:?}",
        result,
    );
}

/// Tier 80c NEGATIVE: insertion must not skip the earliest wrapped empty bucket.
#[test]
fn test_vt_tier80c_skipping_earliest_empty_after_wrap_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_skip_earliest_empty_trace(&mut ctx);

    ctx.push_assert(
        "wrong_skip_earliest_empty",
        "!(slot_state_before.index(probe2) == 0 && slot_state_before.index(probe3) == 0) || \
         slot_state_after.index(probe2) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 80c NEGATIVE: skipping the earliest empty bucket should be rejected, got: {:?}",
        result,
    );
}
