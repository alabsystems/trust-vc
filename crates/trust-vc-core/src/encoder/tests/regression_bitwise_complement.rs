// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn xor_self_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("xor_self", "(x ^ x) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x ^ x should equal 0 when x == 42");
}

#[test]
fn xor_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("xor_zero", "(x ^ 0) == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x ^ 0 should equal 42 when x == 42");
}

#[test]
fn not_not_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12345"));
    ctx.push_obligation(ProofObligation::assert("double_not", "!(!x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!(!x) should equal x when x == 12345");
}

#[test]
fn and_complement_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("and_complement", "(x & !x) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x & !x should equal 0 when x == 42");
}

#[test]
fn or_complement_is_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "or_complement",
        "(x | !x) == 4294967295",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x | !x should equal u32::MAX when x == 42");
}

#[test]
fn xor_complement_is_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "xor_complement",
        "(x ^ !x) == 4294967295",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x ^ !x should equal u32::MAX when x == 42");
}

#[test]
fn not_zero_is_max_u8() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("not_zero", "!x == 255"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!0 should equal 255 for u8");
}

#[test]
fn not_max_is_zero_u8() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("not_max", "!x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!255 should equal 0 for u8");
}

#[test]
fn xor_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 123"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 456"));
    ctx.push_obligation(ProofObligation::assert("xor_comm", "(a ^ b) == (b ^ a)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a ^ b should equal b ^ a");
}

#[test]
fn xor_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "xor_assoc",
        "((a ^ b) ^ c) == (a ^ (b ^ c))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XOR should be associative for 1, 2, and 4");
}
