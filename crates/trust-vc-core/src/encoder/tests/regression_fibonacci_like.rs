// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fib_base_0() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f0", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f0_val", "f0 == 0"));
    ctx.push_obligation(ProofObligation::assert("f0_is_zero", "f0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci base case f0 should equal 0");
}

#[test]
fn fib_base_1() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f1", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f1_val", "f1 == 1"));
    ctx.push_obligation(ProofObligation::assert("f1_is_one", "f1 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci base case f1 should equal 1");
}

#[test]
fn fib_step_2() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f0", i32_ty());
    ctx.declare_var_typed("f1", i32_ty());
    ctx.declare_var_typed("f2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f0_bounds",
        "f0 >= -10000 && f0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f1_bounds",
        "f1 >= -10000 && f1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f2_bounds",
        "f2 >= -10000 && f2 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f0_val", "f0 == 0"));
    ctx.push_obligation(ProofObligation::assume("f1_val", "f1 == 1"));
    ctx.push_obligation(ProofObligation::assume("f2_step", "f2 == f0 + f1"));
    ctx.push_obligation(ProofObligation::assert("f2_is_one", "f2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci step should derive f2 == 1");
}

#[test]
fn fib_step_3() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f1", i32_ty());
    ctx.declare_var_typed("f2", i32_ty());
    ctx.declare_var_typed("f3", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f1_bounds",
        "f1 >= -10000 && f1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f2_bounds",
        "f2 >= -10000 && f2 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f3_bounds",
        "f3 >= -10000 && f3 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f1_val", "f1 == 1"));
    ctx.push_obligation(ProofObligation::assume("f2_val", "f2 == 1"));
    ctx.push_obligation(ProofObligation::assume("f3_step", "f3 == f1 + f2"));
    ctx.push_obligation(ProofObligation::assert("f3_is_two", "f3 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci step should derive f3 == 2");
}

#[test]
fn fib_step_4() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f2", i32_ty());
    ctx.declare_var_typed("f3", i32_ty());
    ctx.declare_var_typed("f4", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f2_bounds",
        "f2 >= -10000 && f2 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f3_bounds",
        "f3 >= -10000 && f3 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f4_bounds",
        "f4 >= -10000 && f4 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f2_val", "f2 == 1"));
    ctx.push_obligation(ProofObligation::assume("f3_val", "f3 == 2"));
    ctx.push_obligation(ProofObligation::assume("f4_step", "f4 == f2 + f3"));
    ctx.push_obligation(ProofObligation::assert("f4_is_three", "f4 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci step should derive f4 == 3");
}

#[test]
fn fib_step_5() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f3", i32_ty());
    ctx.declare_var_typed("f4", i32_ty());
    ctx.declare_var_typed("f5", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f3_bounds",
        "f3 >= -10000 && f3 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f4_bounds",
        "f4 >= -10000 && f4 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f5_bounds",
        "f5 >= -10000 && f5 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f3_val", "f3 == 2"));
    ctx.push_obligation(ProofObligation::assume("f4_val", "f4 == 3"));
    ctx.push_obligation(ProofObligation::assume("f5_step", "f5 == f3 + f4"));
    ctx.push_obligation(ProofObligation::assert("f5_is_five", "f5 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci step should derive f5 == 5");
}

#[test]
fn fib_step_6() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f4", i32_ty());
    ctx.declare_var_typed("f5", i32_ty());
    ctx.declare_var_typed("f6", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f4_bounds",
        "f4 >= -10000 && f4 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f5_bounds",
        "f5 >= -10000 && f5 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f6_bounds",
        "f6 >= -10000 && f6 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f4_val", "f4 == 3"));
    ctx.push_obligation(ProofObligation::assume("f5_val", "f5 == 5"));
    ctx.push_obligation(ProofObligation::assume("f6_step", "f6 == f4 + f5"));
    ctx.push_obligation(ProofObligation::assert("f6_is_eight", "f6 == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fibonacci step should derive f6 == 8");
}

#[test]
fn fib_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f4", i32_ty());
    ctx.declare_var_typed("f5", i32_ty());
    ctx.declare_var_typed("f6", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f4_val", "f4 == 3"));
    ctx.push_obligation(ProofObligation::assume("f5_val", "f5 == 5"));
    ctx.push_obligation(ProofObligation::assume("f6_val", "f6 == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "strictly_increasing",
        "f4 < f5 && f5 < f6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Concrete Fibonacci values should be strictly increasing",
    );
}

#[test]
fn fib_sum_property() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f0", i32_ty());
    ctx.declare_var_typed("f1", i32_ty());
    ctx.declare_var_typed("f2", i32_ty());
    ctx.declare_var_typed("f3", i32_ty());
    ctx.declare_var_typed("f4", i32_ty());
    ctx.declare_var_typed("f5", i32_ty());
    ctx.declare_var_typed("s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "f0_bounds",
        "f0 >= -10000 && f0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f1_bounds",
        "f1 >= -10000 && f1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f2_bounds",
        "f2 >= -10000 && f2 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f3_bounds",
        "f3 >= -10000 && f3 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f4_bounds",
        "f4 >= -10000 && f4 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f5_bounds",
        "f5 >= -10000 && f5 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s_bounds",
        "s >= -10000 && s <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("f0_val", "f0 == 0"));
    ctx.push_obligation(ProofObligation::assume("f1_val", "f1 == 1"));
    ctx.push_obligation(ProofObligation::assume("f2_val", "f2 == 1"));
    ctx.push_obligation(ProofObligation::assume("f3_val", "f3 == 2"));
    ctx.push_obligation(ProofObligation::assume("f4_val", "f4 == 3"));
    ctx.push_obligation(ProofObligation::assume("f5_val", "f5 == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sum_def",
        "s == f0 + f1 + f2 + f3 + f4 + f5",
    ));
    ctx.push_obligation(ProofObligation::assert("sum_is_twelve", "s == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Concrete Fibonacci prefix sum should equal 12");
}

#[test]
fn lucas_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("l0", i32_ty());
    ctx.declare_var_typed("l1", i32_ty());
    ctx.declare_var_typed("l2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "l0_bounds",
        "l0 >= -10000 && l0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l1_bounds",
        "l1 >= -10000 && l1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l2_bounds",
        "l2 >= -10000 && l2 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("l0_val", "l0 == 2"));
    ctx.push_obligation(ProofObligation::assume("l1_val", "l1 == 1"));
    ctx.push_obligation(ProofObligation::assume("l2_step", "l2 == l0 + l1"));
    ctx.push_obligation(ProofObligation::assert("l2_is_three", "l2 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Lucas step should derive l2 == 3");
}
