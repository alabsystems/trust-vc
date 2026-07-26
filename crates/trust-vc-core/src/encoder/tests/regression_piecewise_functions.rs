// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn abs_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_7", "y == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(7) = 7");
}

#[test]
fn abs_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_5", "y == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(-5) = 5");
}

#[test]
fn abs_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_0", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "abs(0) = 0");
}

#[test]
fn sign_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("s", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "s == if x > 0 { 1 } else { if x < 0 { 0 - 1 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("s_is_1", "s == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(10) = 1");
}

#[test]
fn sign_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("s", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "s == if x > 0 { 1 } else { if x < 0 { 0 - 1 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("s_is_neg1", "s == 0 - 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(-3) = -1");
}

#[test]
fn sign_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("s", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "s == if x > 0 { 1 } else { if x < 0 { 0 - 1 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("s_is_0", "s == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(0) = 0");
}

#[test]
fn clamp_below() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_0", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(-5, 0, 10) = 0");
}

#[test]
fn clamp_above() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_10", "y == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(15, 0, 10) = 10");
}

#[test]
fn clamp_in_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_5", "y == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(5, 0, 10) = 5");
}

#[test]
fn step_function() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("threshold", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("threshold_val", "threshold == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x >= threshold { 100 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_0", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "step(3, threshold=5) = 0");
}
