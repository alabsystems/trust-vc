// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn not_and_is_or_not_concrete_tt() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_true", "b == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_and_tt",
        "!(a != 0 && b != 0) == (a == 0 || b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(true && true) should equal false || false for integer-backed booleans",
    );
}

#[test]
fn not_and_is_or_not_concrete_tf() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_false", "b == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_and_tf",
        "!(a != 0 && b != 0) == (a == 0 || b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(true && false) should equal false || true for integer-backed booleans",
    );
}

#[test]
fn not_and_is_or_not_concrete_ff() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_false", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_false", "b == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_and_ff",
        "!(a != 0 && b != 0) == (a == 0 || b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(false && false) should equal true || true for integer-backed booleans",
    );
}

#[test]
fn not_or_is_and_not_concrete_tt() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_true", "b == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_or_tt",
        "!(a != 0 || b != 0) == (a == 0 && b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(true || true) should equal false && false for integer-backed booleans",
    );
}

#[test]
fn not_or_is_and_not_concrete_tf() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_false", "b == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_or_tf",
        "!(a != 0 || b != 0) == (a == 0 && b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(true || false) should equal false && true for integer-backed booleans",
    );
}

#[test]
fn not_or_is_and_not_concrete_ff() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_false", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_false", "b == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_or_ff",
        "!(a != 0 || b != 0) == (a == 0 && b == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(false || false) should equal true && true for integer-backed booleans",
    );
}

#[test]
fn double_negation_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_true", "a == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "double_neg_true",
        "!!(a != 0) == (a != 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "double negation should preserve a true integer-backed boolean",
    );
}

#[test]
fn double_negation_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_false", "a == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "double_neg_false",
        "!!(a != 0) == (a != 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "double negation should preserve a false integer-backed boolean",
    );
}

#[test]
fn bitwise_de_morgan_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("mask", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xF0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("mask_val", "mask == 255"));
    ctx.push_obligation(ProofObligation::assert(
        "bitwise_de_morgan_and",
        "((a & b) ^ mask) == ((a ^ mask) | (b ^ mask))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise De Morgan should hold for concrete 8-bit-style AND under mask 255",
    );
}

#[test]
fn bitwise_de_morgan_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("mask", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xF0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("mask_val", "mask == 255"));
    ctx.push_obligation(ProofObligation::assert(
        "bitwise_de_morgan_or",
        "((a | b) ^ mask) == ((a ^ mask) & (b ^ mask))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise De Morgan should hold for concrete 8-bit-style OR under mask 255",
    );
}
