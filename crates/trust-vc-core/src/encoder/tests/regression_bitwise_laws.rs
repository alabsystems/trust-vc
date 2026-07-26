//! Bitwise operation law regression tests.
//!
//! Verify that bitwise AND, OR, XOR, NOT, and shift operations
//! satisfy fundamental algebraic laws.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn bitwise_and_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assert("comm", "a & b == b & a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND is commutative");
}

#[test]
fn bitwise_or_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assert("comm", "a | b == b | a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR is commutative");
}

#[test]
fn bitwise_xor_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assert("comm", "a ^ b == b ^ a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XOR is commutative");
}

#[test]
fn bitwise_and_identity() {
    // a & 0xFFFFFFFF == a for u32
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("id", "a & 4294967295 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND with all-ones is identity");
}

#[test]
fn bitwise_or_identity() {
    // a | 0 == a
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("id", "a | 0 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR with zero is identity");
}

#[test]
fn bitwise_xor_self_is_zero() {
    // a ^ a == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("zero", "a ^ a == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XOR with self is zero");
}

#[test]
fn bitwise_and_zero() {
    // a & 0 == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("zero", "a & 0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND with zero is zero");
}

#[test]
fn bitwise_and_idempotent() {
    // a & a == a
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("idem", "a & a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND is idempotent");
}

#[test]
fn bitwise_or_idempotent() {
    // a | a == a
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assert("idem", "a | a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR is idempotent");
}

#[test]
fn bitwise_shift_left_right_roundtrip() {
    // (a << 4) >> 4 == a & 0x0FFFFFFF for u32 (top 4 bits cleared)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bounded", "a <= 268435455"));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "(a << 4) >> 4 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shift left then right preserves value when bounded",
    );
}
