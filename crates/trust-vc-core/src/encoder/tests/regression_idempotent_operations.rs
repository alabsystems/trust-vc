// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn and_self_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("and_self", "(x & x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "x & x should preserve x when x == 42");
}

#[test]
fn or_self_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("or_self", "(x | x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "x | x should preserve x when x == 42");
}

#[test]
fn max_self_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "max_self",
        "if x > x { x } else { x } == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(x, x) should preserve x when x == 7");
}

#[test]
fn min_self_is_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "min_self",
        "if x < x { x } else { x } == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(x, x) should preserve x when x == 7");
}

#[test]
fn double_negation_bool() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "double_negation_bool",
        "!!(a != 0) == (a != 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "double negation should preserve the integer-backed boolean when a == 1",
    );
}

#[test]
fn clamp_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("clamped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 50"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "clamped_def",
        "clamped == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "clamp_idempotent",
        "if clamped < lo { lo } else { if clamped > hi { hi } else { clamped } } == clamped",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clamping an already clamped value should preserve it",
    );
}

#[test]
fn abs_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("abs1", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "abs1_def",
        "abs1 == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "abs_idempotent",
        "if abs1 >= 0 { abs1 } else { 0 - abs1 } == abs1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "taking abs twice should preserve a positive absolute value",
    );
}

#[test]
fn abs_idempotent_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("abs1", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -3"));
    ctx.push_obligation(ProofObligation::assume(
        "abs1_def",
        "abs1 == if x >= 0 { x } else { 0 - x }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "abs_idempotent_negative",
        "if abs1 >= 0 { abs1 } else { 0 - abs1 } == abs1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "taking abs twice should preserve the positive result from -3",
    );
}

#[test]
fn xor_self_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 99"));
    ctx.push_obligation(ProofObligation::assert("xor_self", "(x ^ x) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "x ^ x should be zero when x == 99");
}

#[test]
fn zero_addition_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "zero_addition_identity",
        "x + 0 == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "adding zero should preserve x when x == 42");
}
