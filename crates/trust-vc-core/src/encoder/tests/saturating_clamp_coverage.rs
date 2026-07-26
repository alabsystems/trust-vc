//! Coverage tests for `saturating.rs` — BV and Int-mode saturating clamping.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `clamp_to_bounds`, `clamp_unsigned`, and `clamp_signed` in saturating.rs
//! had zero dedicated tests. Existing tests (saturating_missing_bounds.rs,
//! ir_soundness_2100.rs) only exercise error paths and general soundness —
//! none verify that the clamping semantics produce correct concrete values.
//!
//! Each test is DISCRIMINATING: verifying a specific clamped value that would
//! be wrong under wrapping, checked, or unclamped semantics.

use super::*;

// ========================================================================
// Unsigned saturating add
// ========================================================================

/// DISCRIMINATING: u8::saturating_add clamps overflow to 255 (MAX).
///
/// 200u8.saturating_add(100) == 255, NOT 44 (wrapping) or error (checked).
/// If the encoder used wrapping semantics, the result would be 44.
#[test]
fn test_saturating_add_u8_overflow_clamps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_add",
        "x.saturating_add(100) == 255",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200u8.saturating_add(100) should clamp to 255");
}

/// DISCRIMINATING NEGATIVE: wrapping value 44 must NOT be the saturating result.
#[test]
fn test_saturating_add_u8_overflow_not_wrapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    // 44 is the wrapping_add result — saturating should reject this
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_wrong",
        "x.saturating_add(100) == 44",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "200u8.saturating_add(100) == 44 should be counterexample (wrapping, not saturating)",
    );
}

// ========================================================================
// Unsigned saturating sub
// ========================================================================

/// DISCRIMINATING: u8::saturating_sub clamps underflow to 0.
///
/// 10u8.saturating_sub(20) == 0, NOT 246 (wrapping).
#[test]
fn test_saturating_sub_u8_underflow_clamps_to_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_10", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub",
        "x.saturating_sub(20) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10u8.saturating_sub(20) should clamp to 0");
}

/// DISCRIMINATING NEGATIVE: wrapping value 246 must NOT be the saturating result.
#[test]
fn test_saturating_sub_u8_underflow_not_wrapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_10", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_wrong",
        "x.saturating_sub(20) == 246",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "10u8.saturating_sub(20) == 246 should be counterexample (wrapping, not saturating)",
    );
}

// ========================================================================
// Unsigned saturating mul
// ========================================================================

/// DISCRIMINATING: u8::saturating_mul clamps overflow to 255 (MAX).
///
/// 200u8.saturating_mul(2) == 255, NOT 144 (wrapping).
#[test]
fn test_saturating_mul_u8_overflow_clamps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_200", "x == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_mul",
        "x.saturating_mul(2) == 255",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200u8.saturating_mul(2) should clamp to 255");
}

// ========================================================================
// Signed saturating add — positive overflow
// ========================================================================

/// DISCRIMINATING: i8::saturating_add clamps positive overflow to 127 (MAX).
///
/// 120i8.saturating_add(120) == 127, NOT -16 (wrapping) or error.
#[test]
fn test_saturating_add_i8_pos_overflow_clamps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_120", "x == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_signed",
        "x.saturating_add(120) == 127",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "120i8.saturating_add(120) should clamp to 127");
}

// ========================================================================
// Signed saturating add — negative overflow
// ========================================================================

/// DISCRIMINATING: i8::saturating_add clamps negative overflow to -128 (MIN).
///
/// (-120i8).saturating_add(-120) == -128, NOT 16 (wrapping).
#[test]
fn test_saturating_add_i8_neg_overflow_clamps_to_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_neg120", "x == -120"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_neg",
        "x.saturating_add(-120) == -128",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(-120i8).saturating_add(-120) should clamp to -128",
    );
}

// ========================================================================
// Signed saturating sub — positive overflow (pos - neg)
// ========================================================================

/// DISCRIMINATING: i8::saturating_sub positive overflow clamps to 127 (MAX).
///
/// 100i8.saturating_sub(-100) == 127, NOT -56 (wrapping).
/// Positive minus negative overflows when result exceeds MAX.
#[test]
fn test_saturating_sub_i8_pos_overflow_clamps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_100", "x == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_pos",
        "x.saturating_sub(-100) == 127",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100i8.saturating_sub(-100) should clamp to 127");
}

// ========================================================================
// Signed saturating sub — negative overflow (neg - pos)
// ========================================================================

/// DISCRIMINATING: i8::saturating_sub negative overflow clamps to -128 (MIN).
///
/// (-100i8).saturating_sub(100) == -128, NOT 56 (wrapping).
#[test]
fn test_saturating_sub_i8_neg_overflow_clamps_to_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_neg100", "x == -100"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_neg",
        "x.saturating_sub(100) == -128",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(-100i8).saturating_sub(100) should clamp to -128");
}

// ========================================================================
// Signed saturating mul
// ========================================================================

/// DISCRIMINATING: i8::saturating_mul clamps positive overflow to 127 (MAX).
///
/// 100i8.saturating_mul(2) == 127, NOT -56 (wrapping).
#[test]
fn test_saturating_mul_i8_pos_overflow_clamps_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_100", "x == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_mul_signed",
        "x.saturating_mul(2) == 127",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100i8.saturating_mul(2) should clamp to 127");
}

/// DISCRIMINATING: i8::saturating_mul clamps negative overflow to -128 (MIN).
///
/// (-100i8).saturating_mul(2) == -128, NOT 56 (wrapping).
#[test]
fn test_saturating_mul_i8_neg_overflow_clamps_to_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_neg100", "x == -100"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_mul_neg",
        "x.saturating_mul(2) == -128",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(-100i8).saturating_mul(2) should clamp to -128");
}

// ========================================================================
// No-overflow baseline — saturating returns exact result when within bounds
// ========================================================================

/// CONTROL: saturating_add within bounds returns exact result (no clamping).
///
/// 50u8.saturating_add(30) == 80 (no overflow, same as regular add).
/// This baseline ensures the saturating path doesn't unconditionally clamp.
#[test]
fn test_saturating_add_u8_no_overflow_exact() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_50", "x == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_ok",
        "x.saturating_add(30) == 80",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "50u8.saturating_add(30) should be exactly 80 (no clamp)",
    );
}

/// CONTROL: signed saturating_sub within bounds returns exact result.
///
/// 50i8.saturating_sub(30) == 20 (no overflow, same as regular sub).
#[test]
fn test_saturating_sub_i8_no_overflow_exact() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_is_50", "x == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_ok",
        "x.saturating_sub(30) == 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "50i8.saturating_sub(30) should be exactly 20 (no clamp)",
    );
}
