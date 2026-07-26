// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn prepend_increases_length() {
    let mut ctx = VerificationContext::new();
    for v in &["len", "new_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 3"));
    ctx.push_obligation(ProofObligation::assume("new_len_def", "new_len == len + 1"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_len == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prepend increases length by 1");
}

#[test]
fn remove_decreases_length() {
    let mut ctx = VerificationContext::new();
    for v in &["len", "new_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 5"));
    ctx.push_obligation(ProofObligation::assume("new_len_def", "new_len == len - 1"));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_len == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove decreases length by 1");
}

#[test]
fn empty_list_length_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("is_empty", i32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "empty_def",
        "is_empty == if len == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("empty", "is_empty == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "length 0 = empty");
}

#[test]
fn prepend_then_head() {
    let mut ctx = VerificationContext::new();
    for v in &["value", "head_after"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 42"));
    // After prepend, head is the prepended value
    ctx.push_obligation(ProofObligation::assume("head_def", "head_after == value"));
    ctx.push_obligation(ProofObligation::assert("head_is_42", "head_after == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prepend(42).head() = 42");
}

#[test]
fn two_prepends_head_is_last() {
    let mut ctx = VerificationContext::new();
    for v in &["first", "second", "head"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("first_val", "first == 10"));
    ctx.push_obligation(ProofObligation::assume("second_val", "second == 20"));
    // prepend(first) then prepend(second): head = second (LIFO)
    ctx.push_obligation(ProofObligation::assume("head_def", "head == second"));
    ctx.push_obligation(ProofObligation::assert("lifo", "head == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prepend is LIFO: head is last prepended");
}

#[test]
fn append_preserves_head() {
    let mut ctx = VerificationContext::new();
    for v in &["head_before", "head_after", "appended"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hb", "head_before == 5"));
    ctx.push_obligation(ProofObligation::assume("app", "appended == 99"));
    // Appending to the end doesn't change head
    ctx.push_obligation(ProofObligation::assume(
        "head_after_def",
        "head_after == head_before",
    ));
    ctx.push_obligation(ProofObligation::assert("head_same", "head_after == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "append preserves head element");
}

#[test]
fn concatenate_lengths() {
    let mut ctx = VerificationContext::new();
    for v in &["len_a", "len_b", "len_concat"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("la", "len_a == 3"));
    ctx.push_obligation(ProofObligation::assume("lb", "len_b == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "lc_def",
        "len_concat == len_a + len_b",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "len_concat == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concat lengths: 3 + 4 = 7");
}

#[test]
fn reverse_preserves_length() {
    let mut ctx = VerificationContext::new();
    for v in &["len", "rev_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 5"));
    ctx.push_obligation(ProofObligation::assume("rev_def", "rev_len == len"));
    ctx.push_obligation(ProofObligation::assert("same_len", "rev_len == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reverse preserves length");
}

#[test]
fn nth_element_after_prepend() {
    // After prepend(x), element[0] = x, element[1] = old head
    let mut ctx = VerificationContext::new();
    for v in &["old_head", "new_val", "elem0", "elem1"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oh", "old_head == 10"));
    ctx.push_obligation(ProofObligation::assume("nv", "new_val == 20"));
    ctx.push_obligation(ProofObligation::assume("e0_def", "elem0 == new_val"));
    ctx.push_obligation(ProofObligation::assume("e1_def", "elem1 == old_head"));
    ctx.push_obligation(ProofObligation::assert("e0_is_20", "elem0 == 20"));
    ctx.push_obligation(ProofObligation::assert("e1_is_10", "elem1 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "after prepend: [0]=new, [1]=old_head");
}

#[test]
fn split_at_preserves_total_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "total_len",
        "split_pos",
        "left_len",
        "right_len",
        "combined",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("total", "total_len == 10"));
    ctx.push_obligation(ProofObligation::assume("split", "split_pos == 4"));
    ctx.push_obligation(ProofObligation::assume("left_def", "left_len == split_pos"));
    ctx.push_obligation(ProofObligation::assume(
        "right_def",
        "right_len == total_len - split_pos",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "combined_def",
        "combined == left_len + right_len",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conserved",
        "combined == total_len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "split at 4: 4 + 6 = 10");
}
