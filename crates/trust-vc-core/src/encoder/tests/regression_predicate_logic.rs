// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn modus_ponens() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x + 1"));
    ctx.push_obligation(ProofObligation::assert("y_positive", "y > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 5 and y == x + 1 should imply y > 0");
}

#[test]
fn contrapositive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("not_positive", "!(x > 0)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 0 should imply !(x > 0)");
}

#[test]
fn conjunction_elimination() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("both_positive", "x > 0 && y > 0"));
    ctx.push_obligation(ProofObligation::assert("x_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x > 0 && y > 0 should imply x > 0");
}

#[test]
fn conjunction_elimination_right() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("both_positive", "x > 0 && y > 0"));
    ctx.push_obligation(ProofObligation::assert("y_positive", "y > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x > 0 && y > 0 should imply y > 0");
}

#[test]
fn disjunction_from_truth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("nonzero_sign", "x > 0 || x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 5 should imply x > 0 || x < 0");
}

#[test]
fn exclusive_cases() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "zero_only_case",
        "!(x > 0) && !(x < 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 0 should be neither positive nor negative");
}

#[test]
fn trichotomy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounded", "x >= -100 && x <= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "trichotomy",
        "x < 0 || x == 0 || x > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded i32 values should satisfy trichotomy");
}

#[test]
fn transitivity_of_less() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert("ordered", "a < b && b < c"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 < 2 && 2 < 3 should verify");
}

#[test]
fn negation_of_equality() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 6"));
    ctx.push_obligation(ProofObligation::assert("not_equal", "x != y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 and 6 should be unequal");
}

#[test]
fn conditional_reasoning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x > 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_one", "y == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 10 should select the then-branch for y");
}
