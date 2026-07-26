// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn max_of_two_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "max_result",
        "if a >= b { a } else { b } == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(5, 3) should be 5");
}

#[test]
fn min_of_two_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "min_result",
        "if a <= b { a } else { b } == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(5, 3) should be 3");
}

#[test]
fn abs_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "abs_result",
        "if x >= 0 { x } else { -x } == 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(7) should be 7");
}

#[test]
fn abs_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -7"));
    ctx.push_obligation(ProofObligation::assert(
        "abs_result",
        "if x >= 0 { x } else { -x } == 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(-7) should be 7");
}

#[test]
fn clamp_lower() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "clamp_lower_result",
        "if x < lo { lo } else { x } == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamping -5 to [0, 10] should yield 0");
}

#[test]
fn clamp_upper() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "clamp_upper_result",
        "if x > hi { hi } else { x } == 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamping 15 to [0, 10] should yield 10");
}

#[test]
fn clamp_in_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "clamp_in_range_result",
        "if x < lo { lo } else { if x > hi { hi } else { x } } == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamping 5 to [0, 10] should preserve 5");
}

#[test]
fn sign_function_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_result",
        "if x > 0 { 1 } else { if x < 0 { -1 } else { 0 } } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(42) should be 1");
}

#[test]
fn sign_function_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_result",
        "if x > 0 { 1 } else { if x < 0 { -1 } else { 0 } } == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(0) should be 0");
}

#[test]
fn sign_function_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -42"));
    ctx.push_obligation(ProofObligation::assert(
        "sign_result",
        "if x > 0 { 1 } else { if x < 0 { -1 } else { 0 } } == -1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(-42) should be -1");
}
