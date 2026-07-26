// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn event_sequence_number_monotonic() {
    let mut ctx = VerificationContext::new();
    for v in &["seq1", "seq2", "seq3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1", "seq1 == 100"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "seq2 == seq1 + 1"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "seq3 == seq2 + 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mono",
        "seq1 < seq2 && seq2 < seq3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "event sequence: 100 < 101 < 102");
}

#[test]
fn aggregate_state_from_events() {
    // balance = sum of deposits - sum of withdrawals
    let mut ctx = VerificationContext::new();
    for v in &["deposit1", "deposit2", "withdrawal1", "balance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d1", "deposit1 == 100"));
    ctx.push_obligation(ProofObligation::assume("d2", "deposit2 == 50"));
    ctx.push_obligation(ProofObligation::assume("w1", "withdrawal1 == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balance == deposit1 + deposit2 - withdrawal1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_120", "balance == 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "aggregate: 100 + 50 - 30 = 120");
}

#[test]
fn snapshot_plus_events_equals_current() {
    let mut ctx = VerificationContext::new();
    for v in &["snapshot", "event1", "event2", "current_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "snapshot == 50"));
    ctx.push_obligation(ProofObligation::assume("e1", "event1 == 10"));
    ctx.push_obligation(ProofObligation::assume("e2", "event2 == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "current_state == snapshot + event1 + event2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "current_state == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "snapshot 50 + events 10+20 = 80");
}

#[test]
fn event_count_increases() {
    let mut ctx = VerificationContext::new();
    for v in &["count_before", "count_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "count_before == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "count_after == count_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "count_after > count_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "event count: 42 → 43");
}

#[test]
fn idempotent_event_replay() {
    // Replaying same event produces same state
    let mut ctx = VerificationContext::new();
    for v in &["state", "event_val", "after_apply1", "after_apply2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 10"));
    ctx.push_obligation(ProofObligation::assume("ev", "event_val == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "aa1_def",
        "after_apply1 == state + event_val",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "aa2_def",
        "after_apply2 == state + event_val",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "same",
        "after_apply1 == after_apply2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "idempotent: two replays produce same state");
}

#[test]
fn event_version_compatibility() {
    let mut ctx = VerificationContext::new();
    for v in &["event_version", "min_supported"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_process", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ev", "event_version == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_supported == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "can_process == if event_version >= min_supported { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("compatible", "can_process == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "event v3 >= min supported v2 → compatible");
}

#[test]
fn projection_tracks_subset() {
    // Projection builds view from subset of events
    let mut ctx = VerificationContext::new();
    for v in &["total_events", "matching_events", "projected_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("te", "total_events == 100"));
    ctx.push_obligation(ProofObligation::assume("me", "matching_events == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "projected_count == matching_events",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "subset",
        "projected_count <= total_events",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "projection 30 <= 100 total events");
}

#[test]
fn causality_ordering() {
    // Event A caused by B → A's seq > B's seq
    let mut ctx = VerificationContext::new();
    for v in &["cause_seq", "effect_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cs", "cause_seq == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "es_def",
        "effect_seq == cause_seq + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("causal", "effect_seq > cause_seq"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "causality: effect seq 51 > cause seq 50");
}

#[test]
fn compaction_reduces_events() {
    let mut ctx = VerificationContext::new();
    for v in &["events_before", "compacted_to", "reduction"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "events_before == 1000"));
    ctx.push_obligation(ProofObligation::assume("ct", "compacted_to == 1")); // single snapshot
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "reduction == events_before - compacted_to",
    ));
    ctx.push_obligation(ProofObligation::assert("is_999", "reduction == 999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compaction: 1000 events → 1 snapshot, saves 999");
}

#[test]
fn stream_position_bookmark() {
    let mut ctx = VerificationContext::new();
    for v in &["bookmark_pos", "events_since", "current_pos"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "bookmark_pos == 500"));
    ctx.push_obligation(ProofObligation::assume("es", "events_since == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "current_pos == bookmark_pos + events_since",
    ));
    ctx.push_obligation(ProofObligation::assert("is_525", "current_pos == 525"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stream: bookmark 500 + 25 events = position 525");
}
