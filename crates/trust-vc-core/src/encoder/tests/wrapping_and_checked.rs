// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Wrapping and checked arithmetic verification tests.
//!
//! Tests for `wrapping_add/sub/mul` (modular arithmetic) and
//! `checked_add/sub/mul` (overflow-checked arithmetic).
//!
//! # Checked semantics note (#1785)
//!
//! TrustVc encodes `checked_*` as overflow-checked arithmetic: compute the BV
//! result (same as `wrapping_*`) and push overflow predicates to a side channel.
//! This does NOT model Rust's `Option<T>` return type (`Some`/`None`).
//! See [`WrappingMode::Checked`] for details.

use super::*;

// ========================================================================
// Wrapping arithmetic — proof_coverage gap (P1-214)
// ========================================================================

/// DISCRIMINATING: wrapping_add computes modular arithmetic.
///
/// u8::wrapping_add wraps on overflow: 200u8.wrapping_add(100) == 44
/// because (200 + 100) mod 256 == 44. If wrapping_add were replaced by
/// regular add, the result would be 300 which is not representable in u8,
/// so the assertion would not verify as Verified.
#[test]
fn test_wrapping_add_u8_overflow_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    // 200 + 100 = 300, mod 256 = 44
    ctx.push_obligation(ProofObligation::assert(
        "wrap_add",
        "x.wrapping_add(100) == 44",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "200u8.wrapping_add(100) should be 44 (modular wrap)",
    );
}

/// DISCRIMINATING: wrapping_sub computes modular arithmetic.
///
/// 10u8.wrapping_sub(20) == 246 because (10 - 20) mod 256 == 246.
/// If wrapping_sub were regular sub, the result would be -10 which is
/// not representable as u8 and would not match 246.
#[test]
fn test_wrapping_sub_u8_underflow_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_10", "x == 10"));
    // 10 - 20 in u8 wraps to 256 - 10 = 246
    ctx.push_obligation(ProofObligation::assert(
        "wrap_sub",
        "x.wrapping_sub(20) == 246",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10u8.wrapping_sub(20) should be 246 (modular wrap)",
    );
}

/// DISCRIMINATING: wrapping_mul computes modular arithmetic.
///
/// 200u8.wrapping_mul(2) == 144 because (200 * 2) mod 256 == 144.
/// If wrapping_mul were regular mul, the result would be 400 which
/// does not fit in u8.
#[test]
fn test_wrapping_mul_u8_overflow_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    // 200 * 2 = 400, mod 256 = 144
    ctx.push_obligation(ProofObligation::assert(
        "wrap_mul",
        "x.wrapping_mul(2) == 144",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "200u8.wrapping_mul(2) should be 144 (modular wrap)",
    );
}

/// CONTROL: wrapping_add on non-overflowing values behaves like regular add.
#[test]
fn test_wrapping_add_no_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_is_10", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "wrap_add_normal",
        "x.wrapping_add(5) == 15",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10u32.wrapping_add(5) should be 15 (no wrap needed)",
    );
}

/// DISCRIMINATING: wrapping_add wrong arg count returns error.
///
/// If encode_wrapping accepted 0 or 2+ args, this would not return Error.
#[test]
fn test_wrapping_add_wrong_arg_count_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("bad_call", "x.wrapping_add() == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "wrapping_add() with no args should return Error");
}

// ========================================================================
// Overflow-checked arithmetic (#1785) — proof_coverage gap (P1-214)
//
// These test the overflow-checked encoding (not Rust's Option<T> semantics).
// The encoder computes the BV result and asserts no overflow via side-channel.
// ========================================================================

/// FIXED: checked_add on u8 correctly uses unsigned signedness (#1987).
///
/// 100u8.checked_add(50) = 150 fits in u8 (max 255), so no overflow.
/// Previously this was a false positive because the literal 50 caused
/// encode_checked to use signed overflow checks (150 > 127 = i8::MAX).
///
/// DISCRIMINATING: With the fix, is_signed=false for u8 receiver,
/// so unsigned overflow check correctly passes (150 <= 255).
#[test]
fn test_checked_add_u8_signedness_fixed() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_100", "x == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "checked_ok",
        "x.checked_add(50) == 150",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "100u8.checked_add(50) should verify (150 fits in u8)",
    );
}

/// FIXED: checked_add on u8 detects real unsigned overflow (#1987).
///
/// 200u8.checked_add(100) = 300 > 255, so this overflows in u8.
/// Previously this was a false negative — signed overflow check missed it.
///
/// DISCRIMINATING: With the fix, unsigned overflow is correctly detected
/// (300 > 255), so the assertion about the wrapping result (44) fails.
#[test]
fn test_checked_add_u8_overflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "checked_overflow",
        "x.checked_add(100) == 44",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "200u8.checked_add(100) should detect unsigned overflow (300 > 255)",
    );
}

/// FIXED: checked_sub on u8 detects real unsigned underflow (#1987).
///
/// 10u8.checked_sub(20) underflows (10 - 20 < 0 for unsigned).
/// Previously missed because signed underflow check passed.
#[test]
fn test_checked_sub_u8_underflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_10", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "checked_underflow",
        "x.checked_sub(20) == 246",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "10u8.checked_sub(20) should detect unsigned underflow",
    );
}

/// FIXED: checked_mul on u8 detects real unsigned overflow (#1987).
///
/// 200u8.checked_mul(2) = 400 > 255, so this overflows in u8.
/// Previously missed because signed overflow check passed.
#[test]
fn test_checked_mul_u8_overflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "checked_mul_overflow",
        "x.checked_mul(2) == 144",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "200u8.checked_mul(2) should detect unsigned overflow (400 > 255)",
    );
}
