// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn i8_add_wraps_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == -56"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 addition should wrap 100 + 100 to -56");
}

#[test]
fn i8_add_wraps_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == -100"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == 56"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 addition should wrap -100 + -100 to 56");
}

#[test]
fn i8_max_plus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 127"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + 1 == -128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 max plus one should wrap to -128");
}

#[test]
fn i8_min_minus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -128"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - 1 == 127"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 min minus one should wrap to 127");
}

#[test]
fn i16_max_plus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 16 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 32767"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + 1 == -32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i16 max plus one should wrap to -32768");
}

#[test]
fn i16_min_minus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 16 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -32768"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - 1 == 32767"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i16 min minus one should wrap to 32767");
}

#[test]
fn i32_max_plus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + 1 == -2147483648"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 max plus one should wrap to -2147483648");
}

#[test]
fn i32_min_minus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - 1 == 2147483647"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 min minus one should wrap to 2147483647");
}

#[test]
fn i8_mul_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 16"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a * b == -112"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 multiplication should wrap 16 * 9 to -112");
}

#[test]
fn i8_negate_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -128"));
    ctx.push_obligation(ProofObligation::assert("wraps", "-a == -128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negating i8 min should wrap back to -128");
}
