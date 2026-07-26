// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn u8_add_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 addition should wrap 200 + 100 to 44");
}

#[test]
fn u8_sub_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - b == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 subtraction should wrap 0 - 1 to 255");
}

#[test]
fn u8_mul_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 16"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 17"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a * b == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 multiplication should wrap 16 * 17 to 16");
}

#[test]
fn u16_add_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 65535"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u16 addition should wrap 65535 + 1 to 0");
}

#[test]
fn u16_sub_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - b == 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u16 subtraction should wrap 0 - 1 to 65535");
}

#[test]
fn u32_add_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4294967295"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 addition should wrap max + 1 to 0");
}

#[test]
fn u32_sub_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a - b == 4294967295"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 subtraction should wrap 0 - 1 to max");
}

#[test]
fn u8_double_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + a == 144"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 doubling should wrap 200 + 200 to 144");
}

#[test]
fn u8_triple_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a + a + a == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 triple add should wrap 300 to 44");
}

#[test]
fn u32_mul_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 65536"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 65537"));
    ctx.push_obligation(ProofObligation::assert("wraps", "a * b == 65536"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 multiplication should wrap to 65536");
}
