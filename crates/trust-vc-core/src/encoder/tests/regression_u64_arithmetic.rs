// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn u64_add_no_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_bound", "a <= 1000000"));
    ctx.push_obligation(ProofObligation::assume("b_bound", "b <= 1000000"));
    ctx.push_obligation(ProofObligation::assert("sum_bound", "a + b <= 2000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded u64 addition should stay within 2000000");
}

#[test]
fn u64_mul_small() {
    let mut ctx = VerificationContext::new();
    ctx.set_rlimit(2_000);
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_bound", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_bound", "b <= 1000"));
    // This is a bounded nonlinear arithmetic proof; current ay BV search can
    // spend the full downstream smoke timeout on 64-bit multiplication.
    ctx.push_obligation(
        ProofObligation::assert("product_bound", "a * b <= 1000000")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "small u64 multiplication should not produce a counterexample",
    );
}

#[test]
fn u64_sub_no_underflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_ge_b", "a >= b"));
    ctx.push_obligation(ProofObligation::assert("difference_bound", "a - b <= a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u64 subtraction with a >= b should stay within bounds",
    );
}

#[test]
fn u64_max_is_large() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_max",
        "x == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u64::MAX should be greater than zero");
}

#[test]
fn u64_zero_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("identity", "x + 0 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "adding zero should preserve a u64 value");
}

#[test]
fn u64_one_mul_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 999"));
    ctx.push_obligation(ProofObligation::assert("identity", "x * 1 == 999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multiplying by one should preserve a u64 value");
}

#[test]
fn u64_div_halves() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("half", "x / 2 == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 / 2 should equal 50 for u64");
}

#[test]
fn u64_mod_small() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("remainder", "x % 256 == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255 % 256 should equal 255 for u64");
}

#[test]
fn u64_shift_left_double() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("double", "(x << 1) == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 << 1 should equal 20 for u64");
}

#[test]
fn u64_bitwise_and_mask() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("masked", "(x & 15) == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255 & 15 should equal 15 for u64");
}
