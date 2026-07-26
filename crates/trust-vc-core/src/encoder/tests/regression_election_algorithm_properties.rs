// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bully_highest_id_wins() {
    let mut ctx = VerificationContext::new();
    for v in &["id_a", "id_b", "id_c", "winner"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "id_a == 5"));
    ctx.push_obligation(ProofObligation::assume("b", "id_b == 10"));
    ctx.push_obligation(ProofObligation::assume("c", "id_c == 3"));
    ctx.push_obligation(ProofObligation::assume("w_def", "winner == id_b")); // highest
    ctx.push_obligation(ProofObligation::assert("is_10", "winner == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "highest",
        "winner >= id_a && winner >= id_b && winner >= id_c",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bully: highest ID 10 wins");
}

#[test]
fn ring_election_token_passes() {
    let mut ctx = VerificationContext::new();
    for v in &["current_node", "ring_size", "next_node"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cn", "current_node == 4"));
    ctx.push_obligation(ProofObligation::assume("rs", "ring_size == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "nn_def",
        "next_node == if current_node + 1 >= ring_size { 0 } else { current_node + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_node == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ring: node 4 of 5 → wraps to 0");
}

#[test]
fn vote_count_sufficient() {
    let mut ctx = VerificationContext::new();
    for v in &["votes_received", "total_nodes", "needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("elected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vr", "votes_received == 4"));
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "n_def",
        "needed == total_nodes / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "elected == if votes_received >= needed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_elected", "elected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4 votes >= majority of 7 (4)");
}

#[test]
fn epoch_number_increases() {
    let mut ctx = VerificationContext::new();
    for v in &["old_epoch", "new_epoch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oe", "old_epoch == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ne_def",
        "new_epoch == old_epoch + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "new_epoch > old_epoch",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "epoch: 42 → 43");
}

#[test]
fn no_split_brain_with_majority() {
    // Two candidates can't both get majority
    let mut ctx = VerificationContext::new();
    for v in &["total", "votes_a", "votes_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("both_majority", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "total == 5"));
    ctx.push_obligation(ProofObligation::assume("va", "votes_a == 3"));
    ctx.push_obligation(ProofObligation::assume("vb", "votes_b == 2")); // remaining
    ctx.push_obligation(ProofObligation::assume(
        "bm_def",
        "both_majority == if votes_a > total / 2 && votes_b > total / 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_split", "both_majority == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "can't both get majority of 5");
}

#[test]
fn leader_lease_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["lease_start", "lease_duration", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lease_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ls", "lease_start == 1000"));
    ctx.push_obligation(ProofObligation::assume("ld", "lease_duration == 500"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "lv_def",
        "lease_valid == if current_time < lease_start + lease_duration { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "lease_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 1200 < lease end 1500 → valid");
}

#[test]
fn pre_vote_prevents_disruption() {
    // Pre-vote: don't increment term unless majority responds
    let mut ctx = VerificationContext::new();
    for v in &["pre_votes", "needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_start_election", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pv", "pre_votes == 1")); // only self
    ctx.push_obligation(ProofObligation::assume("n", "needed == 3")); // majority of 5
    ctx.push_obligation(ProofObligation::assume(
        "cse_def",
        "can_start_election == if pre_votes >= needed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blocked",
        "can_start_election == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 pre-vote < 3 needed → can't start election");
}

#[test]
fn priority_election_highest_priority_wins() {
    let mut ctx = VerificationContext::new();
    for v in &["priority_a", "priority_b", "winner_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pa", "priority_a == 10"));
    ctx.push_obligation(ProofObligation::assume("pb", "priority_b == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "wp_def",
        "winner_priority == if priority_a > priority_b { priority_a } else { priority_b }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "winner_priority == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "higher priority 20 > 10 wins");
}

#[test]
fn step_down_on_higher_term() {
    let mut ctx = VerificationContext::new();
    for v in &["my_term", "received_term"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_step_down", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt", "my_term == 5"));
    ctx.push_obligation(ProofObligation::assume("rt", "received_term == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "ssd_def",
        "should_step_down == if received_term > my_term { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "step_down",
        "should_step_down == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "received term 7 > my term 5 → step down");
}

#[test]
fn unanimous_agreement() {
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "agreeing_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("unanimous", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("an", "agreeing_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "u_def",
        "unanimous == if agreeing_nodes == total_nodes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("all_agree", "unanimous == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5/5 → unanimous agreement");
}
