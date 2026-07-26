// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn push_increments_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "next_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("depth_val", "depth == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_depth == depth + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("incremented", "next_depth == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "push: depth 3 -> 4");
}

#[test]
fn pop_decrements_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "next_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("depth_val", "depth == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_depth == depth - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("decremented", "next_depth == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pop: depth 3 -> 2");
}

#[test]
fn push_pop_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "after_push", "after_pop"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("depth_val", "depth == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "push_def",
        "after_push == depth + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pop_def",
        "after_pop == after_push - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "after_pop == depth"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "push then pop restores depth");
}

#[test]
fn lifo_order_two_elements() {
    let mut ctx = VerificationContext::new();
    // Push a=10, then b=20. Pop gets b first, then a.
    for v in &["a", "b", "pop1", "pop2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    // LIFO: last pushed is first popped
    ctx.push_obligation(ProofObligation::assume("pop1_def", "pop1 == b"));
    ctx.push_obligation(ProofObligation::assume("pop2_def", "pop2 == a"));
    ctx.push_obligation(ProofObligation::assert("lifo", "pop1 == 20 && pop2 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIFO: push 10, push 20, pop 20, pop 10");
}

#[test]
fn lifo_order_three_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "pop1", "pop2", "pop3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("pop1_def", "pop1 == c"));
    ctx.push_obligation(ProofObligation::assume("pop2_def", "pop2 == b"));
    ctx.push_obligation(ProofObligation::assume("pop3_def", "pop3 == a"));
    ctx.push_obligation(ProofObligation::assert(
        "lifo",
        "pop1 == 3 && pop2 == 2 && pop3 == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIFO: push 1,2,3; pop 3,2,1");
}

#[test]
fn empty_after_push_pop() {
    let mut ctx = VerificationContext::new();
    for v in &["d0", "d1", "d2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d0_val", "d0 == 0"));
    ctx.push_obligation(ProofObligation::assume("d1_def", "d1 == d0 + 1"));
    ctx.push_obligation(ProofObligation::assume("d2_def", "d2 == d1 - 1"));
    ctx.push_obligation(ProofObligation::assert("empty", "d2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "push then pop on empty stack returns to empty");
}

#[test]
fn depth_never_negative() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "after_push"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "depth_bound",
        "depth >= 0 && depth <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "push_def",
        "after_push == depth + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "after_push >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "push always yields depth >= 1");
}

#[test]
fn multiple_push_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["d0", "d1", "d2", "d3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d0_val", "d0 == 0"));
    ctx.push_obligation(ProofObligation::assume("d1_def", "d1 == d0 + 1"));
    ctx.push_obligation(ProofObligation::assume("d2_def", "d2 == d1 + 1"));
    ctx.push_obligation(ProofObligation::assume("d3_def", "d3 == d2 + 1"));
    ctx.push_obligation(ProofObligation::assert("three_deep", "d3 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 pushes from 0 gives depth 3");
}

#[test]
fn peek_does_not_change_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "depth_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("top", i32_ty());
    ctx.push_obligation(ProofObligation::assume("depth_val", "depth == 5"));
    // Peek reads top but does not change depth
    ctx.push_obligation(ProofObligation::assume(
        "depth_after_def",
        "depth_after == depth",
    ));
    ctx.push_obligation(ProofObligation::assert("unchanged", "depth_after == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peek preserves depth");
}

#[test]
fn bounded_stack_overflow_check() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_push", i32_ty());
    ctx.push_obligation(ProofObligation::assume("depth_val", "depth == 10"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "can_push_def",
        "can_push == if depth < capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("full", "can_push == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stack at capacity cannot push");
}
