// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn simple_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 0"));
    ctx.push_obligation(ProofObligation::assume("next_def", "next == state + 1"));
    ctx.push_obligation(ProofObligation::assert("transitioned", "next == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "state 0 -> 1");
}

#[test]
fn two_step_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + 1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + 1"));
    ctx.push_obligation(ProofObligation::assert("final_state", "s2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 -> 1 -> 2");
}

#[test]
fn terminal_state_no_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Terminal state: if state == 3, next == state (no transition)
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if state == 3 { state } else { state + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stuck", "next == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "terminal state stays at 3");
}

#[test]
fn conditional_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 1"));
    ctx.push_obligation(ProofObligation::assume("input_val", "input == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if input == 1 { state + 1 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("advanced", "next == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input=1 triggers transition from 1 to 2");
}

#[test]
fn conditional_no_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "input", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 1"));
    ctx.push_obligation(ProofObligation::assume("input_val", "input == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if input == 1 { state + 1 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert("stayed", "next == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input=0 means no transition");
}

#[test]
fn cyclic_three_states() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == (s0 + 1) % 3"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == (s1 + 1) % 3"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == (s2 + 1) % 3"));
    ctx.push_obligation(ProofObligation::assert("back_to_start", "s3 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3-state cycle returns to 0");
}

#[test]
fn state_bounds_invariant() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "state_bound",
        "state >= 0 && state <= 4",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if state < 4 { state + 1 } else { state }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "next_bound",
        "next >= 0 && next <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transition preserves [0,4] bound");
}

#[test]
fn multi_input_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["state", "a", "b", "next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("state_val", "state == 0"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if a == 1 && b == 1 { 2 } else { if a == 1 { 1 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("both_inputs", "next == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "both inputs active -> state 2");
}

#[test]
fn five_step_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2", "s3", "s4", "s5"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + 1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + 1"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == s2 + 1"));
    ctx.push_obligation(ProofObligation::assume("s4_def", "s4 == s3 + 1"));
    ctx.push_obligation(ProofObligation::assume("s5_def", "s5 == s4 + 1"));
    ctx.push_obligation(ProofObligation::assert("final", "s5 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 increments: 0 -> 5");
}

#[test]
fn error_state_absorbing() {
    let mut ctx = VerificationContext::new();
    for v in &["s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // State -1 is an error/absorbing state
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "s1_def",
        "s1 == if s0 == 0 - 1 { 0 - 1 } else { s0 + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s2_def",
        "s2 == if s1 == 0 - 1 { 0 - 1 } else { s1 + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stays_error", "s2 == 0 - 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "error state is absorbing");
}
