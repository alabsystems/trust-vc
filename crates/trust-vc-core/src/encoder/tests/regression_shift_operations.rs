// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn shift_left_concrete_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 2) == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 << 2 should equal 20 for u32");
}

#[test]
fn shift_right_concrete_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 40"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 3) == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "40 >> 3 should equal 5 for u32");
}

#[test]
fn shift_left_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 0) == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shifting left by zero should preserve i32");
}

#[test]
fn shift_right_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 0) == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shifting right by zero should preserve i32");
}

#[test]
fn shift_left_one_doubles() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 1) == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 << 1 should equal 14 for u32");
}

#[test]
fn shift_right_one_halves() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 1) == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 >> 1 should equal 50 for u32");
}

#[test]
fn shift_left_by_four() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 4) == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 4 should equal 16 for u64");
}

#[test]
fn shift_right_by_four() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 256"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 4) == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "256 >> 4 should equal 16 for u64");
}

#[test]
fn shift_and_mask() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("masked", "((x << 8) >> 8) == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shifting 255 left then right by 8 should preserve u32",
    );
}

#[test]
fn shift_left_adds_zeros() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assert("masked", "((x << 4) & 15) == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "left shift should add zeros in the low bits");
}
