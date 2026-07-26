// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn increment_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 5"));
    ctx.push_obligation(ProofObligation::assume("next_def", "next == count + 1"));
    ctx.push_obligation(ProofObligation::assert("incremented", "next == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "counter: 5 -> 6");
}

#[test]
fn modular_counter_wraps() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "modulus", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 9"));
    ctx.push_obligation(ProofObligation::assume("modulus_val", "modulus == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (count + 1) % modulus",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps_to_zero", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(9 + 1) % 10 = 0");
}

#[test]
fn modular_counter_no_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "modulus", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 3"));
    ctx.push_obligation(ProofObligation::assume("modulus_val", "modulus == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (count + 1) % modulus",
    ));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "next == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(3 + 1) % 10 = 4");
}

#[test]
fn counter_stays_in_range() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "max_val", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "count_bound",
        "count >= 0 && count < 10",
    ));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_val == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if count + 1 < max_val { count + 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "next >= 0 && next < 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modular counter always in [0, 10)");
}

#[test]
fn decrement_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 5"));
    ctx.push_obligation(ProofObligation::assume("next_def", "next == count - 1"));
    ctx.push_obligation(ProofObligation::assert("decremented", "next == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "counter: 5 -> 4");
}

#[test]
fn up_down_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "up", "down"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 7"));
    ctx.push_obligation(ProofObligation::assume("up_def", "up == count + 1"));
    ctx.push_obligation(ProofObligation::assume("down_def", "down == up - 1"));
    ctx.push_obligation(ProofObligation::assert("back_to_start", "down == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "up then down returns to original");
}

#[test]
fn counter_difference() {
    let mut ctx = VerificationContext::new();
    for v in &["start", "end", "steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("start_val", "start == 3"));
    ctx.push_obligation(ProofObligation::assume("end_val", "end == 8"));
    ctx.push_obligation(ProofObligation::assume("steps_def", "steps == end - start"));
    ctx.push_obligation(ProofObligation::assert("five_steps", "steps == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8 - 3 = 5 steps");
}

#[test]
fn power_of_two_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 255"));
    // Counter wrapping at 256 via bitmask
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (count + 1) & 255",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(255 + 1) & 255 = 0 (mod 256 via bitmask)");
}

#[test]
fn gray_code_step() {
    let mut ctx = VerificationContext::new();
    for v in &["n", "gray"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gray code: g(n) = n ^ (n >> 1)
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("gray_def", "gray == n ^ (n >> 1)"));
    // 5 = 0b101, 5>>1 = 0b010, XOR = 0b111 = 7
    ctx.push_obligation(ProofObligation::assert("gray_val", "gray == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gray(5) = 5 ^ 2 = 7");
}

#[test]
fn sequential_counter_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["c0", "c1", "c2", "c3", "c4", "c5"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c0_val", "c0 == 0"));
    ctx.push_obligation(ProofObligation::assume("c1_def", "c1 == c0 + 1"));
    ctx.push_obligation(ProofObligation::assume("c2_def", "c2 == c1 + 1"));
    ctx.push_obligation(ProofObligation::assume("c3_def", "c3 == c2 + 1"));
    ctx.push_obligation(ProofObligation::assume("c4_def", "c4 == c3 + 1"));
    ctx.push_obligation(ProofObligation::assume("c5_def", "c5 == c4 + 1"));
    ctx.push_obligation(ProofObligation::assert("counted_to_five", "c5 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "counting 0 to 5 via chained increments");
}
