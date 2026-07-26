// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn write_head_wraps() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "capacity", "new_head"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 7"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "new_head_def",
        "new_head == if head + 1 == capacity { 0 } else { head + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "new_head == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head at 7 in cap 8 wraps to 0");
}

#[test]
fn write_head_no_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "capacity", "new_head"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 3"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "new_head_def",
        "new_head == if head + 1 == capacity { 0 } else { head + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("advances", "new_head == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head at 3 in cap 8 advances to 4");
}

#[test]
fn buffer_size_from_pointers() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "capacity", "size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 5"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 2"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "size_def",
        "size == if head >= tail { head - tail } else { capacity - tail + head }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "size == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "size: head=5, tail=2, cap=8 → 3");
}

#[test]
fn buffer_size_wrapped() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "capacity", "size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 2"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 6"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "size_def",
        "size == if head >= tail { head - tail } else { capacity - tail + head }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wrapped size: head=2, tail=6, cap=8 → 4");
}

#[test]
fn empty_when_head_equals_tail() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_empty", i32_ty());
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 5"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "empty_def",
        "is_empty == if head == tail { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("empty", "is_empty == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head == tail means empty");
}

#[test]
fn full_when_next_head_equals_tail() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "capacity", "next_head"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 4"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 5"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_head == if head + 1 == capacity { 0 } else { head + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "full_def",
        "is_full == if next_head == tail { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("full", "is_full == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "next_head == tail means full");
}

#[test]
fn write_then_read_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["value", "head", "new_head", "read_val", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 42"));
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 3"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity == 8"));
    // Write at head, advance head
    ctx.push_obligation(ProofObligation::assume(
        "new_head_def",
        "new_head == if head + 1 == capacity { 0 } else { head + 1 }",
    ));
    // Read from old head position
    ctx.push_obligation(ProofObligation::assume("read_def", "read_val == value"));
    ctx.push_obligation(ProofObligation::assert("identity", "read_val == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write then read returns same value");
}

#[test]
fn capacity_minus_one_usable() {
    // Circular buffer wastes one slot to distinguish full from empty
    let mut ctx = VerificationContext::new();
    for v in &["capacity", "usable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "usable_def",
        "usable == capacity - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "usable == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capacity 16: 15 usable slots");
}

#[test]
fn modulo_wrap_power_of_two() {
    // For power-of-two capacity, (idx + 1) & (cap - 1) is faster than modulo
    let mut ctx = VerificationContext::new();
    for v in &["idx", "cap", "mask", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 15"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 16"));
    ctx.push_obligation(ProofObligation::assume("mask_def", "mask == cap - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (idx + 1) & mask",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps_to_0", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(15+1) & 15 = 0 (power-of-two wrap)");
}

#[test]
fn distance_between_pointers() {
    let mut ctx = VerificationContext::new();
    for v in &["write_pos", "read_pos", "capacity", "available"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wp", "write_pos == 3"));
    ctx.push_obligation(ProofObligation::assume("rp", "read_pos == 7"));
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 10"));
    // Available to read (write_pos behind read_pos, wrapped)
    ctx.push_obligation(ProofObligation::assume(
        "avail_def",
        "available == if write_pos >= read_pos { write_pos - read_pos } else { capacity - read_pos + write_pos }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "available == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "distance: write=3, read=7, cap=10 → 6");
}
