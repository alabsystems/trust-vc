// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn add_no_overflow_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 200"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "sum == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 + 200 = 300 (no overflow for u32)");
}

#[test]
fn add_overflow_u8_wraps() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum"] {
        ctx.declare_var_typed(v, u8_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    // u8: 200 + 100 = 300, wraps to 300 - 256 = 44
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("wraps", "sum == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8: 200 + 100 wraps to 44");
}

#[test]
fn checked_add_safe_path() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 50"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 75"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == a + b"));
    ctx.push_obligation(ProofObligation::assert("safe", "result == 125"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "50 + 75 = 125 within i32 bounds");
}

#[test]
fn saturating_add_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "max_val", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 50"));
    ctx.push_obligation(ProofObligation::assume("max_val_val", "max_val == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if a + b > max_val { max_val } else { a + b }",
    ));
    ctx.push_obligation(ProofObligation::assert("saturated", "result == 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "saturating add: 100+50=150 capped at 120");
}

#[test]
fn sub_no_underflow() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "diff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 30"));
    ctx.push_obligation(ProofObligation::assume("diff_def", "diff == a - b"));
    ctx.push_obligation(ProofObligation::assert("positive", "diff == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 - 30 = 70 (no underflow)");
}

#[test]
fn mul_no_overflow_small() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "prod"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 13"));
    ctx.push_obligation(ProofObligation::assume("prod_def", "prod == a * b"));
    ctx.push_obligation(ProofObligation::assert("correct", "prod == 91"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7 * 13 = 91");
}

#[test]
fn overflow_guard_add() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "safe"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 200"));
    // Guard: both positive, sum > both inputs
    ctx.push_obligation(ProofObligation::assume(
        "safe_def",
        "safe == if a >= 0 && b >= 0 && a + b >= a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("guard_passes", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "overflow guard passes for 100 + 200");
}

#[test]
fn double_width_multiplication() {
    let mut ctx = VerificationContext::new();
    // Use u64 to hold product of two u32 values
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("a_wide", u64_ty());
    ctx.declare_var_typed("b_wide", u64_ty());
    ctx.declare_var_typed("prod", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1000"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2000"));
    ctx.push_obligation(ProofObligation::assume("a_wide_def", "a_wide == a"));
    ctx.push_obligation(ProofObligation::assume("b_wide_def", "b_wide == b"));
    ctx.push_obligation(ProofObligation::assume(
        "prod_def",
        "prod == a_wide * b_wide",
    ));
    ctx.push_obligation(ProofObligation::assert("correct", "prod == 2000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "u64 holds u32*u32: 1000*2000=2000000");
}

#[test]
fn negate_min_signed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("neg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 100"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg == 0 - x"));
    ctx.push_obligation(ProofObligation::assert("positive", "neg == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negating -100 gives 100");
}

#[test]
fn shift_overflow_guard() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "shift", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("shift_val", "shift == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == x << shift",
    ));
    ctx.push_obligation(ProofObligation::assert("shifted", "result == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1 << 4 = 16");
}
