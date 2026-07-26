// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bounded_add_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "a >= 0 && a <= 1000 && b >= 0 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sum_in_range",
        "a + b >= 0 && a + b <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded i32 addition should stay within range");
}

#[test]
fn bounded_sub_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "a >= b && a <= 1000"));
    ctx.push_obligation(ProofObligation::assert("diff_bounded", "a - b <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded u32 subtraction should not underflow");
}

#[test]
fn bounded_mul_small() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "a >= 0 && a <= 100 && b >= 0 && b <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("product_nonnegative", "a * b >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "small nonnegative product should stay nonnegative");
}

#[test]
fn bounded_div_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "a > 0 && a <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "quotient_nonnegative",
        "a / 2 >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "positive bounded division should stay nonnegative");
}

#[test]
fn bounded_negate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "a >= -1000 && a <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "negated_in_range",
        "-a >= -1000 && -a <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded i32 negation should stay within range");
}

#[test]
fn bounded_increment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("below_max", "x < 4294967295"));
    ctx.push_obligation(ProofObligation::assert("increments", "x + 1 > x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 increment below max should not wrap");
}

#[test]
fn bounded_decrement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("decrements", "x - 1 < x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 decrement above zero should not wrap");
}

#[test]
fn bounded_double() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("half_max", "x <= 2147483647"));
    ctx.push_obligation(ProofObligation::assert("double_monotone", "x + x >= x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "doubling up to half max should not wrap");
}

#[test]
fn add_preserves_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "a < b && c >= 0 && c <= 100 && a >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("order_preserved", "a + c <= b + c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "adding the same bounded nonnegative value should preserve order",
    );
}

#[test]
fn sub_preserves_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "a < b && c >= 0 && c <= 100 && a >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("order_preserved", "a - c <= b - c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "subtracting the same bounded nonnegative value should preserve order",
    );
}
