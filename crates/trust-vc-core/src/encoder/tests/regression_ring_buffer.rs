// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wrap_around_basic() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "cap", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 4"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (idx + 1) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps_to_zero", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(4+1) % 5 = 0");
}

#[test]
fn no_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "cap", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 2"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (idx + 1) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "next == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(2+1) % 8 = 3 (no wrap)");
}

#[test]
fn full_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["i0", "i1", "i2", "i3", "i4", "cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 4"));
    ctx.push_obligation(ProofObligation::assume("i0_val", "i0 == 0"));
    ctx.push_obligation(ProofObligation::assume("i1_def", "i1 == (i0 + 1) % cap"));
    ctx.push_obligation(ProofObligation::assume("i2_def", "i2 == (i1 + 1) % cap"));
    ctx.push_obligation(ProofObligation::assume("i3_def", "i3 == (i2 + 1) % cap"));
    ctx.push_obligation(ProofObligation::assume("i4_def", "i4 == (i3 + 1) % cap"));
    ctx.push_obligation(ProofObligation::assert("returns_to_start", "i4 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4 steps in capacity-4 ring returns to 0");
}

#[test]
fn distance_forward() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "cap", "count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 3"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 7"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "count_def",
        "count == (tail - head) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("count_is_4", "count == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "distance from head=3 to tail=7 in cap=10 is 4");
}

#[test]
fn distance_wrapped() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "cap", "count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 7"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 3"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "count_def",
        "count == (cap + tail - head) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("count_is_6", "count == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "wrapped distance from 7 to 3 in cap=10 is 6");
}

#[test]
fn empty_buffer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head", u32_ty());
    ctx.declare_var_typed("tail", u32_ty());
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 5"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 5"));
    ctx.push_obligation(ProofObligation::assert("empty", "head == tail"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head == tail means empty");
}

#[test]
fn one_element() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 3"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "tail_def",
        "tail == (head + 1) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "one_elem",
        "tail == 4 && tail != head",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "one element: head=3, tail=4");
}

#[test]
fn power_of_two_modulo() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idx", u32_ty());
    ctx.declare_var_typed("wrapped", u32_ty());
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 19"));
    ctx.push_obligation(ProofObligation::assume("wrapped_def", "wrapped == idx & 7"));
    ctx.push_obligation(ProofObligation::assert("wrapped_is_3", "wrapped == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "19 & 7 = 3 (mod 8 via bitmask)");
}

#[test]
fn advance_by_two() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "cap", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 6"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (idx + 2) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("next_is_0", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(6+2) % 8 = 0");
}

#[test]
fn half_full() {
    let mut ctx = VerificationContext::new();
    for v in &["head", "tail", "cap", "size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 0"));
    ctx.push_obligation(ProofObligation::assume("tail_val", "tail == 4"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "size_def",
        "size == (tail - head) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("half", "size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4 elements in capacity-8 buffer");
}
