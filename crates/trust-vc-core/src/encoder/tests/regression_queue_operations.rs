// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn enqueue_increases_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 3"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size + 1"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "enqueue: size 3 → 4");
}

#[test]
fn dequeue_decreases_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 3"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size - 1"));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_size == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dequeue: size 3 → 2");
}

#[test]
fn fifo_order() {
    // Enqueue a, b; dequeue returns a first
    let mut ctx = VerificationContext::new();
    for v in &["first_in", "second_in", "first_out"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fi", "first_in == 10"));
    ctx.push_obligation(ProofObligation::assume("si", "second_in == 20"));
    ctx.push_obligation(ProofObligation::assume("fo_def", "first_out == first_in"));
    ctx.push_obligation(ProofObligation::assert("fifo", "first_out == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO: enqueue 10, 20; dequeue returns 10");
}

#[test]
fn empty_after_enqueue_dequeue() {
    let mut ctx = VerificationContext::new();
    for v in &["size_init", "after_enqueue", "after_dequeue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("si", "size_init == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ae_def",
        "after_enqueue == size_init + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ad_def",
        "after_dequeue == after_enqueue - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("empty", "after_dequeue == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "enqueue then dequeue returns to empty");
}

#[test]
fn deque_push_front() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size", "front"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("value", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "size == 2"));
    ctx.push_obligation(ProofObligation::assume("v", "value == 42"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size + 1"));
    ctx.push_obligation(ProofObligation::assume("front_def", "front == 42"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 3"));
    ctx.push_obligation(ProofObligation::assert("front_is_val", "front == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deque push_front: size grows, front = value");
}

#[test]
fn deque_push_back() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("back", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "size == 2"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size + 1"));
    ctx.push_obligation(ProofObligation::assume("back_def", "back == 99"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 3"));
    ctx.push_obligation(ProofObligation::assert("back_is_99", "back == 99"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deque push_back: size grows, back = 99");
}

#[test]
fn deque_pop_front_pop_back() {
    // Push 1, 2, 3; pop_front=1, pop_back=3
    let mut ctx = VerificationContext::new();
    for v in &["front", "back"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "front == 1"));
    ctx.push_obligation(ProofObligation::assume("b", "back == 3"));
    ctx.push_obligation(ProofObligation::assert("front_is_1", "front == 1"));
    ctx.push_obligation(ProofObligation::assert("back_is_3", "back == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deque: front=1, back=3");
}

#[test]
fn bounded_queue_reject_when_full() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_enqueue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "size == 10"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "can_enqueue == if size < capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("blocked", "can_enqueue == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "full queue rejects enqueue");
}

#[test]
fn priority_queue_dequeue_min() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "dequeued"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "deq_def",
        "dequeued == if a <= b && a <= c { a } else { if b <= c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("min_dequeued", "dequeued == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "priority queue dequeues min: 2");
}

#[test]
fn queue_size_non_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("size", u32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "size == 0"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "size >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "queue size is always >= 0 (u32)");
}
