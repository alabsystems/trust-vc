// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn majority_quorum() {
    // Majority: > n/2 nodes must agree
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "votes", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_quorum", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("v", "votes == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "threshold == total_nodes / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hq_def",
        "has_quorum == if votes >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("quorum", "has_quorum == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 of 5 votes >= majority (3)");
}

#[test]
fn two_quorums_overlap() {
    // Any two majorities share at least one member
    let mut ctx = VerificationContext::new();
    for v in &["n", "q1", "q2", "overlap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("q1_val", "q1 == 3")); // majority 1
    ctx.push_obligation(ProofObligation::assume("q2_val", "q2 == 3")); // majority 2
                                                                       // overlap >= q1 + q2 - n
    ctx.push_obligation(ProofObligation::assume("o_def", "overlap == q1 + q2 - n"));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "overlap >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two majorities of 5 overlap by at least 1");
}

#[test]
fn leader_election_single_leader() {
    let mut ctx = VerificationContext::new();
    for v in &["term", "leader_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_leader", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "term == 5"));
    ctx.push_obligation(ProofObligation::assume("li", "leader_id == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_leader == if leader_id > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_leader == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leader 2 in term 5 is valid");
}

#[test]
fn term_monotonically_increases() {
    let mut ctx = VerificationContext::new();
    for v in &["current_term", "new_term"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ct", "current_term == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_term == current_term + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "new_term > current_term",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "term 10 → 11: monotonically increases");
}

#[test]
fn log_entry_committed() {
    // Entry committed when replicated on majority
    let mut ctx = VerificationContext::new();
    for v in &["replicated_count", "total_nodes", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("committed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "replicated_count == 4"));
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "threshold == total_nodes / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "committed == if replicated_count >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_committed", "committed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4 of 7 replicas >= majority (4)");
}

#[test]
fn byzantine_fault_tolerance() {
    // BFT: tolerate f faults with 3f+1 total nodes
    let mut ctx = VerificationContext::new();
    for v in &["faults", "min_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "faults == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mn_def",
        "min_nodes == 3 * faults + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "min_nodes == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "BFT: 1 fault → need 4 nodes (3f+1)");
}

#[test]
fn heartbeat_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["last_heartbeat", "current_time", "timeout"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timed_out", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lh", "last_heartbeat == 100"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 300"));
    ctx.push_obligation(ProofObligation::assume("to", "timeout == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timed_out == if current_time - last_heartbeat > timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "timeout_detected",
        "timed_out == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "300 - 100 = 200 > 150 timeout → timed out");
}

#[test]
fn log_index_sequential() {
    let mut ctx = VerificationContext::new();
    for v in &["prev_index", "new_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pi", "prev_index == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "new_index == prev_index + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("sequential", "new_index == 43"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "log index: 42 → 43");
}

#[test]
fn split_vote_no_leader() {
    // Equal split: no majority
    let mut ctx = VerificationContext::new();
    for v in &["votes_a", "votes_b", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_wins", i32_ty());
    ctx.declare_var_typed("b_wins", i32_ty());
    ctx.push_obligation(ProofObligation::assume("va", "votes_a == 2"));
    ctx.push_obligation(ProofObligation::assume("vb", "votes_b == 2"));
    ctx.push_obligation(ProofObligation::assume("t_def", "total == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "a_wins == if votes_a > total / 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bw_def",
        "b_wins == if votes_b > total / 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_winner_a", "a_wins == 0"));
    ctx.push_obligation(ProofObligation::assert("no_winner_b", "b_wins == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2/4 split: no majority winner");
}

#[test]
fn commit_index_advances() {
    let mut ctx = VerificationContext::new();
    for v in &["old_commit", "new_commit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_commit == 10"));
    ctx.push_obligation(ProofObligation::assume("nc", "new_commit == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "advances",
        "new_commit > old_commit",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "commit index: 10 → 15");
}
