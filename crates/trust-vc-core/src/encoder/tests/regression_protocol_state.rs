// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Protocol states encoded as integers:
// 0=Init, 1=SynSent, 2=SynAck, 3=Established, 4=FinWait, 5=Closed

#[test]
fn init_to_syn_sent() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 0 { 1 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_syn_sent", "next_state == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Init → SynSent");
}

#[test]
fn syn_sent_to_syn_ack() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 1 { 2 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_syn_ack", "next_state == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynSent → SynAck");
}

#[test]
fn three_step_handshake() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("init", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "step1",
        "s1 == if s0 == 0 { 1 } else { s0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "step2",
        "s2 == if s1 == 1 { 2 } else { s1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "step3",
        "s3 == if s2 == 2 { 3 } else { s2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("established", "s3 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Init → SynSent → SynAck → Established");
}

#[test]
fn invalid_transition_blocked() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // From Init (0), can only go to SynSent (1), not Established (3)
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 0 { 1 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "not_established",
        "next_state != 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cannot skip to Established from Init");
}

#[test]
fn close_from_established() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 3 { 4 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("fin_wait", "next_state == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Established → FinWait");
}

#[test]
fn fin_to_closed() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 4 { 5 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("closed", "next_state == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FinWait → Closed");
}

#[test]
fn closed_is_terminal() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 5"));
    // Closed stays closed for any event
    ctx.push_obligation(ProofObligation::assume(
        "transition",
        "next_state == if state == 5 { 5 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("stays_closed", "next_state == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Closed is terminal");
}

#[test]
fn sequence_number_increments() {
    let mut ctx = VerificationContext::new();
    for v in &["seq_num", "next_seq", "payload_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("seq", "seq_num == 1000"));
    ctx.push_obligation(ProofObligation::assume("payload", "payload_len == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_seq == seq_num + payload_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1100", "next_seq == 1100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seq number advances by payload length");
}

#[test]
fn ack_matches_next_expected() {
    let mut ctx = VerificationContext::new();
    for v in &["received_seq", "received_len", "expected_ack"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rseq", "received_seq == 500"));
    ctx.push_obligation(ProofObligation::assume("rlen", "received_len == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ack_def",
        "expected_ack == received_seq + received_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_700", "expected_ack == 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ACK = received_seq + len = 700");
}

#[test]
fn retransmit_timer_doubling() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout", "retry1", "retry2", "retry3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t0", "timeout == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "r1_def",
        "retry1 == timeout + timeout",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "r2_def",
        "retry2 == retry1 + retry1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "r3_def",
        "retry3 == retry2 + retry2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "retry1 == 2"));
    ctx.push_obligation(ProofObligation::assert("is_4", "retry2 == 4"));
    ctx.push_obligation(ProofObligation::assert("is_8", "retry3 == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exponential backoff: 1 → 2 → 4 → 8");
}
