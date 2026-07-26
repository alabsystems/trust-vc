// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn square_of_three() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_is_9", "sq == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3^2 = 9");
}

#[test]
fn square_of_negative() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 4"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_is_16", "sq == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(-4)^2 = 16");
}

#[test]
fn square_of_zero() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_is_0", "sq == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0^2 = 0");
}

#[test]
fn square_of_one() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_is_1", "sq == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1^2 = 1");
}

#[test]
fn difference_of_squares() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "a", "b", "sq_a", "sq_b", "diff", "sum_ab", "diff_ab", "prod",
    ] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("sq_a_def", "sq_a == a * a"));
    ctx.push_obligation(ProofObligation::assume("sq_b_def", "sq_b == b * b"));
    ctx.push_obligation(ProofObligation::assume("diff_def", "diff == sq_a - sq_b"));
    ctx.push_obligation(ProofObligation::assume("sum_ab_def", "sum_ab == a + b"));
    ctx.push_obligation(ProofObligation::assume("diff_ab_def", "diff_ab == a - b"));
    ctx.push_obligation(ProofObligation::assume(
        "prod_def",
        "prod == sum_ab * diff_ab",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "diff == prod"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "a^2 - b^2 = (a+b)(a-b) for 5,3");
}

#[test]
fn square_plus_one() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq", "sp"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assume("sp_def", "sp == sq + 1"));
    ctx.push_obligation(ProofObligation::assert("sp_is_50", "sp == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7^2 + 1 = 50");
}

#[test]
fn sum_of_first_two_squares() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sq1", i32_ty());
    ctx.declare_var_typed("sq4", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sq1_val", "sq1 == 1"));
    ctx.push_obligation(ProofObligation::assume("sq4_val", "sq4 == 4"));
    ctx.push_obligation(ProofObligation::assert("sum_is_5", "sq1 + sq4 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 + 4 = 5 (1^2 + 2^2)");
}

#[test]
fn square_larger_than_base() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_gt_x", "sq > x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5^2 = 25 > 5");
}

#[test]
fn perfect_square_check() {
    let mut ctx = VerificationContext::new();
    for v in &["n", "root", "sq"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 49"));
    ctx.push_obligation(ProofObligation::assume("root_val", "root == 7"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == root * root"));
    ctx.push_obligation(ProofObligation::assert("perfect", "sq == n"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7^2 = 49");
}

#[test]
fn pythagorean_triple() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "sa", "sb", "sc"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume("sa_def", "sa == a * a"));
    ctx.push_obligation(ProofObligation::assume("sb_def", "sb == b * b"));
    ctx.push_obligation(ProofObligation::assume("sc_def", "sc == c * c"));
    ctx.push_obligation(ProofObligation::assert("pythagoras", "sa + sb == sc"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3^2 + 4^2 = 5^2");
}
