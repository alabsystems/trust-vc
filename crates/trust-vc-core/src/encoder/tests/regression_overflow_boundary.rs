// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn u8_at_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("still_max", "x == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 max boundary should remain 255");
}

#[test]
fn u8_max_wraps_to_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("wraps_zero", "x + 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 max plus one should wrap to zero");
}

#[test]
fn u8_min_wraps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("wraps_max", "x - 1 == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 zero minus one should wrap to max");
}

#[test]
fn i32_max_plus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("wraps_min", "x + 1 == -2147483648"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 max plus one should wrap to min");
}

#[test]
fn i32_min_minus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("wraps_max", "x - 1 == 2147483647"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 min minus one should wrap to max");
}

#[test]
fn u32_max_is_all_ones() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295"));
    ctx.push_obligation(ProofObligation::assert("wraps_zero", "x + 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 max plus one should wrap to zero");
}

#[test]
fn u32_half_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_half_max", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("next_value", "x + 1 == 2147483648"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 half max plus one should stay in range");
}

#[test]
fn u8_boundary_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.declare_var_typed("y", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 128"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 127"));
    ctx.push_obligation(ProofObligation::assert("boundary_sum", "x + y == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "u8 boundary addition should produce the max in-range value",
    );
}

#[test]
fn i32_zero_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_one", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("zero_boundary", "x - 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "subtracting one from one should reach zero");
}

#[test]
fn u32_powers_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_pow2", "x == 1073741824"));
    ctx.push_obligation(ProofObligation::assert(
        "double_pow2",
        "x + x == 2147483648",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "doubling two to the thirtieth should yield two to the thirty-first",
    );
}
