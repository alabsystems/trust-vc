// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn two_x_plus_three_y() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "x", "y", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 4"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == a * x + b * y",
    ));
    ctx.push_obligation(ProofObligation::assert("result_is_23", "result == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2*4 + 3*5 = 23");
}

#[test]
fn weighted_sum_concrete() {
    let mut ctx = VerificationContext::new();
    for v in &["w1", "w2", "w3", "v1", "v2", "v3", "t1", "t2", "t3", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("w1_val", "w1 == 1"));
    ctx.push_obligation(ProofObligation::assume("w2_val", "w2 == 2"));
    ctx.push_obligation(ProofObligation::assume("w3_val", "w3 == 3"));
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 10"));
    ctx.push_obligation(ProofObligation::assume("v2_val", "v2 == 20"));
    ctx.push_obligation(ProofObligation::assume("v3_val", "v3 == 30"));
    ctx.push_obligation(ProofObligation::assume("t1_def", "t1 == w1 * v1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == w2 * v2"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == w3 * v3"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == t1 + t2 + t3"));
    ctx.push_obligation(ProofObligation::assert("sum_is_140", "sum == 140"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1*10 + 2*20 + 3*30 = 140");
}

#[test]
fn linear_map_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "x", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == a * x + b"));
    ctx.push_obligation(ProofObligation::assert("result_is_42", "result == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "identity linear map: 1*42 + 0 = 42");
}

#[test]
fn sum_of_coefficients() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assert("sum_is_10", "a + b + c == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 + 3 + 5 = 10");
}

#[test]
fn double_equals_add_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("d", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("d_def", "d == x + x"));
    ctx.push_obligation(ProofObligation::assert("d_is_34", "d == 34"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "17 + 17 = 34");
}

#[test]
fn triple_via_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("t", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume("t_def", "t == x + x + x"));
    ctx.push_obligation(ProofObligation::assert("t_is_21", "t == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 + 7 + 7 = 21");
}

#[test]
fn negation_cancels() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("neg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg == 0 - a"));
    ctx.push_obligation(ProofObligation::assert("sum_is_zero", "a + neg == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 + (-10) = 0");
}

#[test]
fn linear_combination_zero() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "x", "y", "ax", "by", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume("ax_def", "ax == a * x"));
    ctx.push_obligation(ProofObligation::assume("by_def", "by == b * y"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == ax + by"));
    ctx.push_obligation(ProofObligation::assert("result_is_zero", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3*5 + 5*(-3) = 0");
}

#[test]
fn affine_transform() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "slope", "intercept", "product", "y"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("slope_val", "slope == 2"));
    ctx.push_obligation(ProofObligation::assume("intercept_val", "intercept == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "product_def",
        "product == slope * x",
    ));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == product + intercept"));
    ctx.push_obligation(ProofObligation::assert("y_is_25", "y == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2*10 + 5 = 25");
}

#[test]
fn difference_of_weighted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "w", "diff", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 6"));
    ctx.push_obligation(ProofObligation::assume("w_val", "w == 3"));
    ctx.push_obligation(ProofObligation::assume("diff_def", "diff == a - b"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == w * diff"));
    ctx.push_obligation(ProofObligation::assert("result_is_neg6", "result == 0 - 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3*(4-6) = -6");
}
