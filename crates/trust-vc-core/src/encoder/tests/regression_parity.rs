// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn even_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("even", "x % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42 should be even");
}

#[test]
fn odd_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 43"));
    ctx.push_obligation(ProofObligation::assert("odd", "x % 2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "43 should be odd");
}

#[test]
fn zero_is_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("zero_even", "x % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 should be even");
}

#[test]
fn double_is_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("double_even", "(x * 2) % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "doubling should preserve evenness");
}

#[test]
fn even_plus_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 6"));
    ctx.push_obligation(ProofObligation::assert("sum_even", "(a + b) % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "even plus even should be even");
}

#[test]
fn odd_plus_odd() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("sum_even", "(a + b) % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "odd plus odd should be even");
}

#[test]
fn even_plus_odd() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("sum_odd", "(a + b) % 2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "even plus odd should be odd");
}

#[test]
fn even_times_any() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert("product_even", "(a * b) % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "even times any value should be even");
}

#[test]
fn bit_test_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("bit_even", "(x & 1) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42 should have low bit cleared");
}

#[test]
fn bit_test_odd() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 43"));
    ctx.push_obligation(ProofObligation::assert("bit_odd", "(x & 1) == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "43 should have low bit set");
}
