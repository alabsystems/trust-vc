//! Ordering and comparison regression tests.
//!
//! Verify that <, <=, >, >=, ==, != behave correctly for all integer widths,
//! including interactions with negation and unsigned types.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn ordering_transitivity_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transitivity of < for i32");
}

#[test]
fn ordering_antisymmetry_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("ba", "b <= a"));
    ctx.push_obligation(ProofObligation::assert("eq", "a == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "antisymmetry of <= for i32");
}

#[test]
fn ordering_totality_i32() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assert("total", "a <= b || b <= a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "totality of <= for i32");
}

#[test]
fn ordering_u32_no_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 values are always >= 0");
}

#[test]
fn ordering_i32_can_be_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert("always_nonneg", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "i32 can be negative - should find counterexample");
}

#[test]
fn ordering_ne_reflexive_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert("not_ne", "!(x != x)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x != x should always be false");
}

#[test]
fn ordering_eq_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert("eq_refl", "x == x"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == x should always be true");
}

#[test]
fn ordering_lt_implies_le() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("le", "a <= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b implies a <= b");
}

#[test]
fn ordering_lt_implies_ne() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("ne", "a != b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b implies a != b");
}

#[test]
fn ordering_u64_transitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.declare_var_typed("c", u64_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transitivity of < for u64");
}

#[test]
fn ordering_signed_unsigned_mismatch_detection() {
    // A signed value at -1 cannot be less than all unsigned values in the
    // unsigned sense.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("neg", "x == -1"));
    ctx.push_obligation(ProofObligation::assert("lt_zero", "x < 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-1 < 0 for signed i32");
}

#[test]
fn ordering_le_ge_equivalence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("le", "a <= b"));
    ctx.push_obligation(ProofObligation::assert("ge", "b >= a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a <= b iff b >= a");
}

#[test]
fn ordering_lt_gt_equivalence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("gt", "b > a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b iff b > a");
}

#[test]
fn ordering_trichotomy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assert("trich", "a < b || a == b || a > b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trichotomy: one of <, ==, > must hold");
}

#[test]
fn ordering_u8_max_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assert("bounded", "x <= 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 is always <= 255");
}
