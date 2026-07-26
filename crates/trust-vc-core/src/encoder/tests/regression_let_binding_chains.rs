// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn single_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_eq_a", "b == a"));
    ctx.push_obligation(ProofObligation::assert("b_is_5", "b == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "b == a and a == 5 should force b == 5");
}

#[test]
fn two_step_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_def", "b == a + 1"));
    ctx.push_obligation(ProofObligation::assume("c_def", "c == b + 1"));
    ctx.push_obligation(ProofObligation::assert("c_is_5", "c == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a=3, b=a+1=4, c=b+1=5");
}

#[test]
fn diamond_dependency() {
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
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x + 3"));
    ctx.push_obligation(ProofObligation::assume("z_def", "z == x + 4"));
    ctx.push_obligation(ProofObligation::assert("sum_check", "y + z == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "y=5, z=6, sum=11");
}

#[test]
fn accumulator_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s0", i32_ty());
    ctx.declare_var_typed("s1", i32_ty());
    ctx.declare_var_typed("s2", i32_ty());
    ctx.declare_var_typed("s3", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + 1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + 2"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == s2 + 3"));
    ctx.push_obligation(ProofObligation::assert("s3_is_6", "s3 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 + 1 + 2 + 3 = 6");
}

#[test]
fn shadow_override() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("x2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x + 5"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "both_correct",
        "y == 15 && x2 == 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "y computed from x=10, x2 independently set to 20");
}

#[test]
fn backward_reference_consistency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a_bound",
        "a >= -1000 && a <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bound",
        "b >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_def", "b == a * 2"));
    ctx.push_obligation(ProofObligation::assert("b_is_14", "b == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7 * 2 = 14 (nonlinear may return Unknown)");
}

#[test]
fn triple_equality_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", i32_ty());
    ctx.declare_var_typed("q", i32_ty());
    ctx.declare_var_typed("r", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p_eq_q", "p == q"));
    ctx.push_obligation(ProofObligation::assume("q_eq_r", "q == r"));
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 42"));
    ctx.push_obligation(ProofObligation::assert("p_is_42", "p == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p == q == r == 42 by transitivity");
}

#[test]
fn computed_then_compared() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("base", i32_ty());
    ctx.declare_var_typed("offset", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "base_bound",
        "base >= -1000 && base <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "offset_bound",
        "offset >= -1000 && offset <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "result_bound",
        "result >= -1000 && result <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("base_val", "base == 100"));
    ctx.push_obligation(ProofObligation::assume("offset_val", "offset == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == base - offset",
    ));
    ctx.push_obligation(ProofObligation::assert("result_is_90", "result == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 - 10 = 90");
}

#[test]
fn conditional_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "x_def",
        "x == if flag == 1 { 10 } else { 20 }",
    ));
    ctx.push_obligation(ProofObligation::assert("x_is_10", "x == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flag=1 selects the then-branch giving x=10");
}

#[test]
fn nested_arithmetic_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a_bound",
        "a >= -1000 && a <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bound",
        "b >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_bound",
        "c >= -1000 && c <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_def", "b == a * a"));
    ctx.push_obligation(ProofObligation::assume("c_def", "c == b * a"));
    ctx.push_obligation(ProofObligation::assert("c_is_8", "c == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2^2=4, 4*2=8 (nonlinear may return Unknown)");
}
