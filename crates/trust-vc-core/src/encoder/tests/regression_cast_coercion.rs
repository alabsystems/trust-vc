//! Regression tests for integer cast and coercion behavior.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn cast_u8_to_u32_preserves_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 value preserved in u32");
}

#[test]
fn cast_i8_to_i32_preserves_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -42"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == -42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 value preserved in i32");
}

#[test]
fn cast_same_width_small_positive_agrees() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 and u32 agree on small positive values");
}

#[test]
fn cast_zero_between_types_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zero is preserved across integer coercions");
}

#[test]
fn cast_u8_max_fits_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 255"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 max fits in u32");
}

#[test]
fn cast_i8_min_preserved_in_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -128"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == -128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i8 min is preserved in i32");
}

#[test]
fn cast_i16_range_in_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 16 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 32767"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 32767"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i16 max preserved in i32");
}

#[test]
fn cast_u16_max_fits_u32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 16 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 65535"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("preserved", "y == 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u16 max preserved in u32");
}

#[test]
fn cast_i32_positive_preserved_across_widths() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 100"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("y_same", "y > 0 && y < 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "positive i32 range preserved in assignment");
}

#[test]
fn cast_u8_add_wraps_at_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    // u8 addition wraps: 200 + 100 = 44 (mod 256)
    ctx.push_obligation(ProofObligation::assert("wraps", "a + b == 44"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 addition wraps at 256");
}
