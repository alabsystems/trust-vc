// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 47 - Lock-free hash set core VCs.
//!
//! VerifyThis 2022 included a lock-free hash set challenge. TrustVc does not yet
//! model CAS or heap ownership directly on the stable bridge, so this tier
//! keeps the competition proof shape on the reliable VerificationPipeline path
//! by phrasing the core obligations as explicit post-state VCs over flat arrays:
//!   - `slot_state: Seq<i64>` where 0 = EMPTY, 1 = LIVE, 2 = TOMBSTONE
//!   - `slot_key:   Seq<i64>` storing concrete keys (`-1` for unused slots)
//!
//! Core obligations:
//!   - insert publishes into the home bucket or the first later probe bucket
//!   - probe chains wrap at the end of the table
//!   - tombstones preserve lookup chains for later live keys
//!   - delete marks TOMBSTONE rather than clearing to EMPTY
//!   - duplicate insert leaves the existing live key in place
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

#[path = "support/verifythis_lock_free_hash_set.rs"]
mod verifythis_lock_free_hash_set_support;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;
use verifythis_lock_free_hash_set_support::{
    assume_distinct_i64, assume_non_sentinel_i64, assume_probe_step, assume_seq_exprs,
    assume_seq_i64, verify_with_pipeline,
};

// ========================================================================
// GROUP A: Insert / publish post-states
// ========================================================================

/// Tier 47a: insert into an empty home bucket publishes the new live slot.
#[test]
fn test_vt_tier47a_insert_into_empty_home_bucket() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("preserved_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[0, 1, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[0, 1, 1, 0]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_before",
        &["-1", "preserved_key", "-1", "-1"],
    );
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["-1", "preserved_key", "target", "-1"],
    );
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 2");
    assume_non_sentinel_i64(&mut ctx, "preserved_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "preserved_key", "target");

    ctx.push_assert("home_is_empty_before", "slot_state_before.index(home) == 0");
    ctx.push_assert("home_is_live_after", "slot_state_after.index(home) == 1");
    ctx.push_assert(
        "inserted_key_visible",
        "slot_key_after.index(home) == target",
    );
    ctx.push_assert(
        "existing_live_bucket_preserved",
        "slot_key_after.index(1) == preserved_key",
    );
    ctx.push_assert("home_in_bounds", "home < n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47a: insert into empty home bucket should verify, got: {:?}",
        result,
    );
}

/// Tier 47b: a collision probes to the next bucket and preserves the live home slot.
#[test]
fn test_vt_tier47b_collision_probes_to_next_bucket() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[0, 0, 1, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[0, 0, 1, 1]);
    assume_seq_exprs(&mut ctx, "slot_key_before", &["-1", "-1", "home_key", "-1"]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["-1", "-1", "home_key", "target"],
    );
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 2");
    assume_non_sentinel_i64(&mut ctx, "home_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "home_key", "target");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert(
        "home_bucket_stays_live",
        "slot_state_after.index(home) == 1",
    );
    ctx.push_assert(
        "home_bucket_keeps_old_key",
        "slot_key_after.index(home) == home_key",
    );
    ctx.push_assert("next_probe_is_three", "probe1 == 3");
    ctx.push_assert(
        "probe_bucket_receives_target",
        "slot_key_after.index(probe1) == target",
    );
    ctx.push_assert(
        "probe_bucket_is_live",
        "slot_state_after.index(probe1) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47b: collision probe should verify, got: {:?}",
        result,
    );
}

/// Tier 47c: a probe from the last bucket wraps around to bucket 0.
#[test]
fn test_vt_tier47c_wraparound_probe_uses_bucket_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tail_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[0, 0, 0, 1]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[1, 0, 0, 1]);
    assume_seq_exprs(&mut ctx, "slot_key_before", &["-1", "-1", "-1", "tail_key"]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["target", "-1", "-1", "tail_key"],
    );
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 3");
    assume_non_sentinel_i64(&mut ctx, "tail_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "tail_key", "target");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert("wraps_to_zero", "probe1 == 0");
    ctx.push_assert(
        "wrapped_bucket_is_live",
        "slot_state_after.index(probe1) == 1",
    );
    ctx.push_assert(
        "wrapped_bucket_stores_target",
        "slot_key_after.index(probe1) == target",
    );
    ctx.push_assert(
        "old_tail_bucket_preserved",
        "slot_key_after.index(home) == tail_key",
    );
    ctx.push_assert("wrapped_probe_in_bounds", "probe1 < n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47c: wraparound probe should verify, got: {:?}",
        result,
    );
}

/// Tier 47d: lookup skips a tombstone and finds a later live key in the cluster.
#[test]
fn test_vt_tier47d_lookup_skips_tombstone_and_finds_later_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("tombstone_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state", &[2, 1, 0, 0]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key",
        &["tombstone_key", "target", "-1", "-1"],
    );
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 0");
    assume_non_sentinel_i64(&mut ctx, "tombstone_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "tombstone_key", "target");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert("home_is_tombstone", "slot_state.index(home) == 2");
    ctx.push_assert("tombstone_is_not_empty", "slot_state.index(home) != 0");
    ctx.push_assert("next_probe_is_one", "probe1 == 1");
    ctx.push_assert("later_bucket_is_live", "slot_state.index(probe1) == 1");
    ctx.push_assert(
        "later_bucket_matches_target",
        "slot_key.index(probe1) == target",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47d: tombstone-skipping lookup should verify, got: {:?}",
        result,
    );
}

/// Tier 47e: delete marks a bucket TOMBSTONE instead of clearing it to EMPTY.
#[test]
fn test_vt_tier47e_delete_marks_tombstone_not_empty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("removed_key", "i64");
    ctx.declare_var_parsed("neighbor_key", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[1, 1, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[2, 1, 0, 0]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_before",
        &["removed_key", "neighbor_key", "-1", "-1"],
    );
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["removed_key", "neighbor_key", "-1", "-1"],
    );
    ctx.declare_var_parsed("home", "u64");

    ctx.push_assume("home_val", "home == 0");
    assume_non_sentinel_i64(&mut ctx, "removed_key");
    assume_non_sentinel_i64(&mut ctx, "neighbor_key");
    assume_distinct_i64(&mut ctx, "removed_key", "neighbor_key");

    ctx.push_assert(
        "removed_bucket_was_live",
        "slot_state_before.index(home) == 1",
    );
    ctx.push_assert(
        "removed_bucket_is_tombstone",
        "slot_state_after.index(home) == 2",
    );
    ctx.push_assert(
        "removed_bucket_not_empty",
        "slot_state_after.index(home) != 0",
    );
    ctx.push_assert(
        "later_live_bucket_stays_visible",
        "slot_key_after.index(1) == neighbor_key",
    );
    ctx.push_assert(
        "later_live_bucket_stays_live",
        "slot_state_after.index(1) == 1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47e: delete-to-tombstone should verify, got: {:?}",
        result,
    );
}

/// Tier 47f: insert reuses a tombstone before probing to a later empty bucket.
#[test]
fn test_vt_tier47f_insert_reuses_tombstone_before_empty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("stale_key", "i64");
    ctx.declare_var_parsed("neighbor_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[2, 1, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[1, 1, 0, 0]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_before",
        &["stale_key", "neighbor_key", "-1", "-1"],
    );
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["target", "neighbor_key", "-1", "-1"],
    );
    ctx.declare_var_parsed("home", "u64");

    ctx.push_assume("home_val", "home == 0");
    assume_non_sentinel_i64(&mut ctx, "stale_key");
    assume_non_sentinel_i64(&mut ctx, "neighbor_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "stale_key", "neighbor_key");
    assume_distinct_i64(&mut ctx, "stale_key", "target");
    assume_distinct_i64(&mut ctx, "neighbor_key", "target");

    ctx.push_assert("home_was_tombstone", "slot_state_before.index(home) == 2");
    ctx.push_assert("home_is_live_after", "slot_state_after.index(home) == 1");
    ctx.push_assert(
        "tombstone_reused_for_target",
        "slot_key_after.index(home) == target",
    );
    ctx.push_assert(
        "tombstone_payload_changes",
        "slot_key_before.index(home) != slot_key_after.index(home)",
    );
    ctx.push_assert(
        "existing_neighbor_preserved",
        "slot_key_after.index(1) == neighbor_key",
    );
    ctx.push_assert(
        "later_empty_slot_stays_empty",
        "slot_state_after.index(2) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47f: tombstone reuse should verify, got: {:?}",
        result,
    );
}

/// Tier 47g: two collisions advance to the second later probe bucket.
#[test]
fn test_vt_tier47g_two_collisions_reach_second_probe_bucket() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("home_key", "i64");
    ctx.declare_var_parsed("probe_key", "i64");
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[1, 1, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[1, 1, 1, 0]);
    assume_seq_exprs(
        &mut ctx,
        "slot_key_before",
        &["home_key", "probe_key", "-1", "-1"],
    );
    assume_seq_exprs(
        &mut ctx,
        "slot_key_after",
        &["home_key", "probe_key", "target", "-1"],
    );
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");
    ctx.declare_var_parsed("probe2", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 0");
    assume_non_sentinel_i64(&mut ctx, "home_key");
    assume_non_sentinel_i64(&mut ctx, "probe_key");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_distinct_i64(&mut ctx, "home_key", "probe_key");
    assume_distinct_i64(&mut ctx, "home_key", "target");
    assume_distinct_i64(&mut ctx, "probe_key", "target");
    assume_probe_step(&mut ctx, "probe1", "home", "n");
    assume_probe_step(&mut ctx, "probe2", "probe1", "n");

    ctx.push_assert(
        "first_probe_hits_live_collision",
        "slot_state_before.index(probe1) == 1",
    );
    ctx.push_assert("second_probe_is_two", "probe2 == 2");
    ctx.push_assert(
        "second_probe_is_live_after",
        "slot_state_after.index(probe2) == 1",
    );
    ctx.push_assert(
        "second_probe_gets_target",
        "slot_key_after.index(probe2) == target",
    );
    ctx.push_assert(
        "earlier_collision_keys_preserved",
        "slot_key_after.index(1) == probe_key",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47g: second-probe insertion should verify, got: {:?}",
        result,
    );
}

/// Tier 47h: duplicate insert leaves the existing live key in place.
#[test]
fn test_vt_tier47h_duplicate_insert_keeps_existing_bucket() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("target", "i64");
    assume_seq_i64(&mut ctx, "slot_state_before", &[1, 0, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_state_after", &[1, 0, 0, 0]);
    assume_seq_exprs(&mut ctx, "slot_key_before", &["target", "-1", "-1", "-1"]);
    assume_seq_exprs(&mut ctx, "slot_key_after", &["target", "-1", "-1", "-1"]);
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 0");
    assume_non_sentinel_i64(&mut ctx, "target");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert(
        "home_bucket_stays_live",
        "slot_state_after.index(home) == 1",
    );
    ctx.push_assert(
        "home_bucket_keeps_target",
        "slot_key_after.index(home) == target",
    );
    ctx.push_assert(
        "duplicate_does_not_allocate_probe",
        "slot_state_after.index(probe1) == 0",
    );
    ctx.push_assert(
        "probe_bucket_stays_unused",
        "slot_key_after.index(probe1) == -1",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 47h: duplicate insert should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Soundness negatives
// ========================================================================

/// Tier 47i: a tombstone must not terminate lookup when a later live key exists.
#[test]
fn test_vt_tier47i_tombstone_must_not_terminate_lookup() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "slot_state", &[2, 1, 0, 0]);
    assume_seq_i64(&mut ctx, "slot_key", &[11, 42, -1, -1]);
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 0");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert(
        "wrong_stop_at_tombstone",
        "!(slot_state.index(home) == 2) || slot_state.index(probe1) == 0",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 47i SOUNDNESS: tombstone stop should be rejected, got: {:?}",
        result,
    );
}

/// Tier 47j: collision insert must not overwrite the existing live home bucket.
#[test]
fn test_vt_tier47j_collision_insert_must_not_overwrite_live_bucket() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "slot_state_after", &[0, 0, 1, 0]);
    assume_seq_i64(&mut ctx, "slot_key_after", &[-1, -1, 42, -1]);
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 2");
    assume_probe_step(&mut ctx, "probe1", "home", "n");

    ctx.push_assert(
        "wrong_collision_poststate",
        "slot_key_after.index(home) == 10 && slot_key_after.index(probe1) == 42",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 47j SOUNDNESS: overwrite-on-collision should be rejected, got: {:?}",
        result,
    );
}
