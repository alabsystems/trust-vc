// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn log_append_increases_index() {
    let mut ctx = VerificationContext::new();
    for v in &["last_index", "new_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("li", "last_index == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "new_index == last_index + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "new_index > last_index",
    ));
    ctx.push_obligation(ProofObligation::assert("is_101", "new_index == 101"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Raft log: index 100 → 101");
}

#[test]
fn commit_index_never_decreases() {
    let mut ctx = VerificationContext::new();
    for v in &["old_commit", "new_commit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_commit == 50"));
    ctx.push_obligation(ProofObligation::assume("nc", "new_commit == 75"));
    ctx.push_obligation(ProofObligation::assert(
        "monotonic",
        "new_commit >= old_commit",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "commit index: 50 → 75 (monotonic)");
}

#[test]
fn majority_quorum_for_commit() {
    let mut ctx = VerificationContext::new();
    for v in &["cluster_size", "acks", "quorum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("committed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "cluster_size == 5"));
    ctx.push_obligation(ProofObligation::assume("a", "acks == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "q_def",
        "quorum == cluster_size / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "committed == if acks >= quorum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_committed", "committed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Raft: 3 acks >= quorum 3 (5/2+1) → committed");
}

#[test]
fn term_monotonicity() {
    let mut ctx = VerificationContext::new();
    for v in &["current_term", "new_term"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ct", "current_term == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_term == current_term + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "new_term > current_term",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Raft term: 5 → 6");
}

#[test]
fn log_matching_property() {
    // If two logs have entry with same index and term, all preceding entries match
    // Simplified: same term at same index → match
    let mut ctx = VerificationContext::new();
    for v in &["log_a_term", "log_b_term", "index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("entries_match", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lat", "log_a_term == 3"));
    ctx.push_obligation(ProofObligation::assume("lbt", "log_b_term == 3"));
    ctx.push_obligation(ProofObligation::assume("i", "index == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "em_def",
        "entries_match == if log_a_term == log_b_term { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("match", "entries_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "log matching: same term 3 at index 42 → match");
}

#[test]
fn leader_completeness() {
    // A committed entry must be present in all future leaders' logs
    // Simplified: leader's last index >= commit index
    let mut ctx = VerificationContext::new();
    for v in &["leader_last_index", "commit_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lli", "leader_last_index == 100"));
    ctx.push_obligation(ProofObligation::assume("ci", "commit_index == 75"));
    ctx.push_obligation(ProofObligation::assert(
        "complete",
        "leader_last_index >= commit_index",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leader completeness: last 100 >= commit 75");
}

#[test]
fn follower_log_replication() {
    let mut ctx = VerificationContext::new();
    for v in &["follower_last", "leader_next_index", "entries_to_send"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fl", "follower_last == 80"));
    ctx.push_obligation(ProofObligation::assume("lni", "leader_next_index == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ets_def",
        "entries_to_send == leader_next_index - follower_last",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "entries_to_send == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "replication: 100 - 80 = 20 entries to send");
}

#[test]
fn snapshot_compacts_log() {
    let mut ctx = VerificationContext::new();
    for v in &["log_length", "snapshot_index", "remaining_log"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ll", "log_length == 10000"));
    ctx.push_obligation(ProofObligation::assume("si", "snapshot_index == 9000"));
    ctx.push_obligation(ProofObligation::assume(
        "rl_def",
        "remaining_log == log_length - snapshot_index",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "remaining_log == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "snapshot: 10000 - 9000 = 1000 remaining");
}

#[test]
fn election_timeout_resets() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed", "timeout", "new_elapsed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("start_election", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "elapsed == 300"));
    ctx.push_obligation(ProofObligation::assume("t", "timeout == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "start_election == if elapsed >= timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume("ne_def", "new_elapsed == 0")); // reset after election
    ctx.push_obligation(ProofObligation::assert("election", "start_election == 1"));
    ctx.push_obligation(ProofObligation::assert("reset", "new_elapsed == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "300ms >= 250ms timeout → start election, reset");
}

#[test]
fn pre_vote_prevents_disruption() {
    let mut ctx = VerificationContext::new();
    for v in &["candidate_log_length", "voter_log_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("grant_pre_vote", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cll",
        "candidate_log_length == 100",
    ));
    ctx.push_obligation(ProofObligation::assume("vll", "voter_log_length == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "gpv_def",
        "grant_pre_vote == if candidate_log_length >= voter_log_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("granted", "grant_pre_vote == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pre-vote: candidate log 100 >= voter 90 → grant");
}
