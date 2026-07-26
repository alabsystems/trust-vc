// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn identity_composition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x"));
    ctx.push_obligation(ProofObligation::assert("y_is_5", "y == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "identity composition should preserve x == 5");
}

#[test]
fn double_then_add_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("doubled", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "doubled_bound",
        "doubled >= -2000 && doubled <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "result_bound",
        "result >= -2001 && result <= 2001",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("doubled_def", "doubled == x + x"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == doubled + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("result_is_7", "result == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "doubling 3 and adding 1 should produce 7");
}

#[test]
fn negate_then_negate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("neg", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "neg_bound",
        "neg >= -1000 && neg <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "result_bound",
        "result >= -1000 && result <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "neg == 0 - x"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == 0 - neg"));
    ctx.push_obligation(ProofObligation::assert("result_is_7", "result == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double negation should recover the original value");
}

#[test]
fn add_then_subtract() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "y_bound",
        "y >= -1000 && y <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "z_bound",
        "z >= -1000 && z <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x + 5"));
    ctx.push_obligation(ProofObligation::assume("z_def", "z == y - 5"));
    ctx.push_obligation(ProofObligation::assert("z_eq_x", "z == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "adding 5 then subtracting 5 should return x");
}

#[test]
fn triple_application() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("z", i32_ty());
    ctx.declare_var_typed("w", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "y_bound",
        "y >= -1000 && y <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "z_bound",
        "z >= -1000 && z <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "w_bound",
        "w >= -1000 && w <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x + 1"));
    ctx.push_obligation(ProofObligation::assume("z_def", "z == y + 1"));
    ctx.push_obligation(ProofObligation::assume("w_def", "w == z + 1"));
    ctx.push_obligation(ProofObligation::assert("w_is_5", "w == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "three chained increments from 2 should produce 5");
}

#[test]
fn square_then_check_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("sq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sq_bound",
        "sq >= 0 && sq <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -3"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "sq == x * x"));
    ctx.push_obligation(ProofObligation::assert("sq_positive", "sq > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "squaring -3 should yield a positive result");
}

#[test]
fn clamp_upper() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("limit", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 150"));
    ctx.push_obligation(ProofObligation::assume("limit_val", "limit == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x > limit { limit } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert("result_is_100", "result == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "upper clamp should select the limit for x = 150");
}

#[test]
fn clamp_lower() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("floor", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -5"));
    ctx.push_obligation(ProofObligation::assume("floor_val", "floor == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x < floor { floor } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert("result_is_0", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lower clamp should select the floor for x = -5");
}

#[test]
fn min_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("m_is_3", "m == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should select the smaller concrete input");
}

#[test]
fn max_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("m_is_7", "m == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max should select the larger concrete input");
}
