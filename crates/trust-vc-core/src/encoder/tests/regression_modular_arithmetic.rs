// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn mod_10_of_20_is_0() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 20"));
    ctx.push_obligation(ProofObligation::assert("mod_zero", "x % 10 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "20 % 10 should equal 0");
}

#[test]
fn mod_10_of_23_is_3() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 23"));
    ctx.push_obligation(ProofObligation::assert("mod_three", "x % 10 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "23 % 10 should equal 3");
}

#[test]
fn mod_self_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("mod_self", "x % x == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x % x should equal 0 when x == 7");
}

#[test]
fn mod_larger_is_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assert("mod_self", "x % 10 == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 % 10 should equal 3");
}

#[test]
fn mod_one_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("mod_one", "x % 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x % 1 should equal 0");
}

#[test]
fn u32_mod_preserves_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_lt_100", "x < 100"));
    ctx.push_obligation(ProofObligation::assert("range_preserved", "x % 100 == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 values below the modulus should be preserved");
}

#[test]
fn i32_mod_positive_divisor_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "x % b >= 0 && x % b < b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 % 4 should be bounded by a positive divisor");
}

#[test]
fn mod_distributes_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "distributes",
        "(a + b) % c == (((a % c) + (b % c)) % c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "modular addition should distribute across remainder",
    );
}

#[test]
fn mod_power_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("pow2", "x % 256 == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255 % 256 should equal 255");
}

#[test]
fn div_mod_reconstruct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 17"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "reconstruct",
        "(a / b) * b + a % b == a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "division and remainder should reconstruct the dividend",
    );
}
