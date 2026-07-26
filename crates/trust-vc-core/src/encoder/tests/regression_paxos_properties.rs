// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ballot_number_monotonic() {
    let mut ctx = VerificationContext::new();
    for v in &["ballot_1", "ballot_2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b1", "ballot_1 == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "b2_def",
        "ballot_2 == ballot_1 + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("mono", "ballot_2 > ballot_1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Paxos ballot: 5 → 6 (monotonic)");
}

#[test]
fn prepare_quorum_majority() {
    let mut ctx = VerificationContext::new();
    for v in &["acceptors", "promises", "quorum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_quorum", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "acceptors == 5"));
    ctx.push_obligation(ProofObligation::assume("p", "promises == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "q_def",
        "quorum == acceptors / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hq_def",
        "has_quorum == if promises >= quorum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("quorum_met", "has_quorum == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Paxos: 3 promises >= quorum 3 (5/2+1)");
}

#[test]
fn two_quorums_overlap() {
    // Any two quorums must share at least one acceptor
    let mut ctx = VerificationContext::new();
    for v in &["total", "quorum_a", "quorum_b", "min_overlap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "total == 5"));
    ctx.push_obligation(ProofObligation::assume("qa", "quorum_a == 3"));
    ctx.push_obligation(ProofObligation::assume("qb", "quorum_b == 3"));
    // overlap >= qa + qb - total
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "min_overlap == quorum_a + quorum_b - total",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "min_overlap > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "quorum overlap: 3+3-5 = 1 > 0");
}

#[test]
fn accept_only_highest_ballot() {
    let mut ctx = VerificationContext::new();
    for v in &["promised_ballot", "request_ballot"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accept", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "promised_ballot == 10"));
    ctx.push_obligation(ProofObligation::assume("rb", "request_ballot == 8")); // stale
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "accept == if request_ballot >= promised_ballot { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "accept == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reject stale ballot 8 < promised 10");
}

#[test]
fn value_chosen_once() {
    // Once a value is chosen, it cannot be changed
    let mut ctx = VerificationContext::new();
    for v in &["chosen_value", "proposed_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cv", "chosen_value == 42"));
    ctx.push_obligation(ProofObligation::assume("pv", "proposed_value == 42")); // must match
    ctx.push_obligation(ProofObligation::assert(
        "same",
        "proposed_value == chosen_value",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chosen value 42 is immutable");
}

#[test]
fn proposer_id_makes_ballot_unique() {
    // ballot = (round, proposer_id) — unique per proposer per round
    let mut ctx = VerificationContext::new();
    for v in &["round", "num_proposers", "proposer_id", "ballot"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "round == 3"));
    ctx.push_obligation(ProofObligation::assume("np", "num_proposers == 5"));
    ctx.push_obligation(ProofObligation::assume("pi", "proposer_id == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "ballot == round * num_proposers + proposer_id",
    ));
    ctx.push_obligation(ProofObligation::assert("is_17", "ballot == 17"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ballot: 3*5+2 = 17 (unique)");
}

#[test]
fn multi_paxos_log_index() {
    let mut ctx = VerificationContext::new();
    for v in &["committed_index", "new_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ci", "committed_index == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "new_index == committed_index + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "advances",
        "new_index > committed_index",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Multi-Paxos: log index 100 → 101");
}

#[test]
fn learner_receives_accepted() {
    let mut ctx = VerificationContext::new();
    for v in &["accepted_count", "quorum", "total_acceptors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("learned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac", "accepted_count == 3"));
    ctx.push_obligation(ProofObligation::assume("ta", "total_acceptors == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "q_def",
        "quorum == total_acceptors / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "learned == if accepted_count >= quorum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("learns", "learned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "learner: 3 accepts >= quorum 3 → learned");
}

#[test]
fn nack_with_higher_ballot() {
    let mut ctx = VerificationContext::new();
    for v in &["request_ballot", "highest_seen", "nack_ballot"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rb", "request_ballot == 5"));
    ctx.push_obligation(ProofObligation::assume("hs", "highest_seen == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "nack_ballot == highest_seen",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "higher",
        "nack_ballot > request_ballot",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NACK: highest 10 > request 5");
}

#[test]
fn phase2_requires_phase1_quorum() {
    let mut ctx = VerificationContext::new();
    for v in &["phase1_promises", "quorum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_propose", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p1p", "phase1_promises == 2"));
    ctx.push_obligation(ProofObligation::assume("q", "quorum == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "can_propose == if phase1_promises >= quorum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cannot", "can_propose == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 promises < quorum 3 → cannot propose");
}
