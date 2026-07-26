//! Mixed integer width regression tests.
//!
//! Verify correct behavior when different integer widths interact.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn mixed_i8_max_is_127() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assert("bounded", "x <= 127"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 is always <= 127");
}

#[test]
fn mixed_i8_min_is_neg128() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assert("bounded", "x >= -128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 is always >= -128");
}

#[test]
fn mixed_u8_max_is_255() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assert("bounded", "x <= 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 is always <= 255");
}

#[test]
fn mixed_i16_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 16 });
    ctx.push_obligation(ProofObligation::assert("lower", "x >= -32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i16 >= -32768");
}

#[test]
fn mixed_u16_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.push_obligation(ProofObligation::assert("upper", "x <= 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u16 <= 65535");
}

#[test]
fn mixed_u64_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u64 is always >= 0");
}

#[test]
fn mixed_i32_within_i8_range_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo", "x >= -128"));
    ctx.push_obligation(ProofObligation::assume("hi", "x <= 127"));
    ctx.push_obligation(ProofObligation::assert("in_i8", "x >= -128 && x <= 127"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 in i8 range satisfies i8 bounds");
}

#[test]
fn mixed_u8_add_safe_small() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("a_bound", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_bound", "b <= 100"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "a + b <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "small u8 add does not wrap");
}

#[test]
fn mixed_u8_add_can_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assert("always_sum_correct", "a + b >= a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "u8 addition can overflow and wrap");
}

#[test]
fn mixed_i32_mul_i8_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_concrete", "a == -10"));
    ctx.push_obligation(ProofObligation::assume("b_concrete", "b == 10"));
    ctx.push_obligation(
        ProofObligation::assert("product_bounded", "a * b >= -100")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "small i32 product is bounded");
}
