// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// DFA states encoded as u32: 0=start, 1..N=intermediate, N+1=accept, N+2=reject

#[test]
fn single_transition_accept() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 0"));
    ctx.push_obligation(ProofObligation::assume("i", "input == 1"));
    // On input 1 from state 0, go to accept state 2
    ctx.push_obligation(ProofObligation::assume(
        "trans",
        "next_state == if state == 0 && input == 1 { 2 } else { 3 }",
    ));
    ctx.push_obligation(ProofObligation::assert("accepted", "next_state == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DFA: state 0 + input 1 → accept");
}

#[test]
fn single_transition_reject() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 0"));
    ctx.push_obligation(ProofObligation::assume("i", "input == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "trans",
        "next_state == if state == 0 && input == 1 { 2 } else { 3 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "next_state == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DFA: state 0 + input 0 → reject");
}

#[test]
fn two_step_acceptance() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "i0", "s1", "i1", "s2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("i0_val", "i0 == 1"));
    ctx.push_obligation(ProofObligation::assume("i1_val", "i1 == 1"));
    // 0 + input 1 → 1
    ctx.push_obligation(ProofObligation::assume(
        "trans1",
        "s1 == if s0 == 0 && i0 == 1 { 1 } else { 3 }",
    ));
    // 1 + input 1 → 2 (accept)
    ctx.push_obligation(ProofObligation::assume(
        "trans2",
        "s2 == if s1 == 1 && i1 == 1 { 2 } else { 3 }",
    ));
    ctx.push_obligation(ProofObligation::assert("accepted", "s2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DFA: 0 →1→ 1 →1→ accept");
}

#[test]
fn reject_state_is_absorbing() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 3"));
    ctx.push_obligation(ProofObligation::assume("i", "input == 1"));
    // Reject state stays reject for any input
    ctx.push_obligation(ProofObligation::assume(
        "trans",
        "next_state == if state == 3 { 3 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("still_reject", "next_state == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reject state is absorbing");
}

#[test]
fn accept_state_is_final() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("state", u32_ty());
    ctx.declare_var_typed("is_accept", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "state == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "accept_def",
        "is_accept == if state == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("accepted", "is_accept == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "state 2 is accepting");
}

#[test]
fn three_state_cycle() {
    // States: 0 → 1 → 2 → 0 (on input 1)
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "t1",
        "s1 == if s0 == 0 { 1 } else { if s0 == 1 { 2 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "t2",
        "s2 == if s1 == 0 { 1 } else { if s1 == 1 { 2 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "t3",
        "s3 == if s2 == 0 { 1 } else { if s2 == 1 { 2 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("cycles_back", "s3 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3-state cycle: 0→1→2→0");
}

#[test]
fn state_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "num_states"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 2"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_states == 4"));
    ctx.push_obligation(ProofObligation::assert("in_range", "state < num_states"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "state 2 < 4 states");
}

#[test]
fn nfa_two_possible_transitions() {
    // NFA: from state 0 on input 1, can go to state 1 OR state 2
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next_a", "next_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 0"));
    ctx.push_obligation(ProofObligation::assume("i", "input == 1"));
    ctx.push_obligation(ProofObligation::assume("na", "next_a == 1"));
    ctx.push_obligation(ProofObligation::assume("nb", "next_b == 2"));
    ctx.push_obligation(ProofObligation::assert("different", "next_a != next_b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFA: two distinct next states");
}

#[test]
fn epsilon_transition_same_input() {
    // Epsilon transition: state changes without consuming input
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state", "input_pos", "next_input_pos"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 1"));
    ctx.push_obligation(ProofObligation::assume("ns", "next_state == 2"));
    ctx.push_obligation(ProofObligation::assume("ip", "input_pos == 5"));
    // Epsilon transition doesn't advance input
    ctx.push_obligation(ProofObligation::assume(
        "nip",
        "next_input_pos == input_pos",
    ));
    ctx.push_obligation(ProofObligation::assert("same_pos", "next_input_pos == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "epsilon transition preserves input position");
}

#[test]
fn dfa_total_function() {
    // Every (state, input) pair has exactly one transition
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "state == 1"));
    ctx.push_obligation(ProofObligation::assume("i", "input == 0"));
    // Total: always produces a valid next state
    ctx.push_obligation(ProofObligation::assume(
        "trans",
        "next == if state == 0 { if input == 0 { 1 } else { 2 } } else { if input == 0 { 0 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_state", "next <= 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DFA transition always produces valid state");
}
