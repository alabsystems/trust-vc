// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn div_remainder_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "q", "r", "qb", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a / b"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == a % b"));
    ctx.push_obligation(ProofObligation::assume("qb_def", "qb == q * b"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == qb + r"));
    ctx.push_obligation(ProofObligation::assert("identity", "result == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "q*b + r == a for 17/5");
}

#[test]
fn remainder_less_than_divisor() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "r"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == a % b"));
    ctx.push_obligation(ProofObligation::assert("r_bound", "r >= 0 && r < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0 <= 17%5 < 5");
}

#[test]
fn exact_division() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "r"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 20"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == a % b"));
    ctx.push_obligation(ProofObligation::assert("exact", "r == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "20 % 4 == 0");
}

#[test]
fn quotient_concrete() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "q"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a / b"));
    ctx.push_obligation(ProofObligation::assert("q_is_3", "q == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "17 / 5 == 3");
}

#[test]
fn remainder_concrete() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "r"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == a % b"));
    ctx.push_obligation(ProofObligation::assert("r_is_2", "r == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "17 % 5 == 2");
}

#[test]
fn zero_divided() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "q"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a / b"));
    ctx.push_obligation(ProofObligation::assert("q_is_0", "q == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0 / 7 == 0");
}

#[test]
fn self_divided() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "q"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 13"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 13"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a / b"));
    ctx.push_obligation(ProofObligation::assert("q_is_1", "q == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "13 / 13 == 1");
}

#[test]
fn double_then_halve() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "d", "h"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assume("d_def", "d == x + x"));
    ctx.push_obligation(ProofObligation::assume("h_def", "h == d / 2"));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "h == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "15+15=30, 30/2=15");
}

#[test]
fn mod_idempotent_small() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "r"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == a % b"));
    ctx.push_obligation(ProofObligation::assert("r_is_a", "r == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 % 7 == 3 (a < b)");
}

#[test]
fn successive_division() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_def", "b == a / 10"));
    ctx.push_obligation(ProofObligation::assume("c_def", "c == b / 2"));
    ctx.push_obligation(ProofObligation::assert("c_is_5", "c == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100/10=10, 10/2=5");
}
