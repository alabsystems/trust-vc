//! Unsigned arithmetic overflow/underflow behavior tests (#1476).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests verify that the encoder's overflow checks correctly detect
//! unsigned arithmetic overflow (add), underflow (sub), and multiplication
//! overflow for u32 and u8 types.
//!
//! Coverage gap: unsigned_arith_signedness.rs tests signedness discrimination
//! (bvudiv vs bvsdiv). This file tests that overflow checks FIRE when
//! unsigned arithmetic actually overflows/underflows.
//!
//! Discriminating property: with overflow checks enabled, operations that
//! exceed the unsigned range must return Counterexample (overflow detected),
//! while safe operations must verify.

use super::*;

// ========================================================================
// Unsigned addition overflow
// ========================================================================

/// DISCRIMINATING: u32::MAX + 1 must NOT verify — unsigned overflow detected.
///
/// u32::MAX (4294967295) + 1 wraps to 0 in BV arithmetic. The overflow check
/// `bvadd_no_overflow(MAX, 1, false)` must fire, producing a Counterexample.
///
/// Without overflow checks, the BV result 0 would be valid and the
/// assertion `x + 1 == x + 1` (tautology) would verify. It's the overflow
/// check that catches the overflow — making this test discriminating.
#[test]
fn test_unsigned_add_overflow_u32_max_plus_one() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    // u32::MAX
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295"));
    // Tautological assertion: only the overflow check can cause failure
    ctx.push_obligation(ProofObligation::assert("add_taut", "x + 1 == x + 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32::MAX + 1 must NOT verify — unsigned addition overflow detected",
    );
}

/// CONTROL: u32 addition within range should verify with overflow checks.
///
/// 100 + 200 = 300, well within u32 range (max 4294967295). The overflow
/// check passes and the assertion verifies normally.
#[test]
fn test_unsigned_add_safe_u32_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("add_result", "x + 200 == 300"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100u32 + 200 == 300 should verify (no overflow)");
}

/// DISCRIMINATING: u8::MAX + 1 must NOT verify — u8 overflow detected.
///
/// 255u8 + 1 wraps to 0 in 8-bit BV arithmetic. Tests that overflow
/// checks work correctly at the u8 boundary, not just u32.
#[test]
fn test_unsigned_add_overflow_u8_boundary() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 255")); // u8::MAX
    ctx.push_obligation(ProofObligation::assert("add_taut", "x + 1 == x + 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "255u8 + 1 must NOT verify — u8 addition overflow detected",
    );
}

// ========================================================================
// Unsigned subtraction underflow
// ========================================================================

/// DISCRIMINATING: 0u32 - 1 must NOT verify — unsigned underflow detected.
///
/// 0 - 1 wraps to u32::MAX (4294967295) in BV arithmetic. The underflow
/// check `bvsub_no_underflow(0, 1, false)` must fire.
///
/// Without overflow checks, the BV result u32::MAX would be valid.
/// The underflow check is the discriminating mechanism.
#[test]
fn test_unsigned_sub_underflow_u32_zero_minus_one() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    // Tautological assertion: only the underflow check can cause failure
    ctx.push_obligation(ProofObligation::assert("sub_taut", "x - 1 == x - 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "0u32 - 1 must NOT verify — unsigned subtraction underflow detected",
    );
}

/// CONTROL: u32 subtraction within range should verify with overflow checks.
///
/// 200 - 100 = 100, no underflow.
#[test]
fn test_unsigned_sub_safe_u32_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200"));
    ctx.push_obligation(ProofObligation::assert("sub_result", "x - 100 == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200u32 - 100 == 100 should verify (no underflow)");
}

/// DISCRIMINATING: 0u8 - 1 must NOT verify — u8 underflow detected.
///
/// Tests that underflow checks work correctly at the u8 boundary.
#[test]
fn test_unsigned_sub_underflow_u8_boundary() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("sub_taut", "x - 1 == x - 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "0u8 - 1 must NOT verify — u8 subtraction underflow detected",
    );
}

// ========================================================================
// Unsigned multiplication overflow
// ========================================================================

/// DISCRIMINATING: u32::MAX * 2 must NOT verify — unsigned multiplication overflow.
///
/// 4294967295 * 2 = 8589934590, which exceeds u32 range. The overflow
/// check `bvmul_no_overflow(MAX, 2, false)` must fire.
#[test]
fn test_unsigned_mul_overflow_u32_max_times_two() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295")); // u32::MAX
    ctx.push_obligation(ProofObligation::assert("mul_taut", "x * 2 == x * 2"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32::MAX * 2 must NOT verify — unsigned multiplication overflow detected",
    );
}

/// CONTROL: u32 multiplication within range should verify with overflow checks.
///
/// 100 * 200 = 20000, well within u32 range.
#[test]
fn test_unsigned_mul_safe_u32_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("mul_result", "x * 200 == 20000"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100u32 * 200 == 20000 should verify (no overflow)");
}

/// DISCRIMINATING: 200u8 * 2 must NOT verify — u8 multiplication overflow.
///
/// 200 * 2 = 400, which exceeds u8 range (max 255). In BV8 arithmetic,
/// 400 mod 256 = 144. The overflow check must catch this.
#[test]
fn test_unsigned_mul_overflow_u8_boundary() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200"));
    ctx.push_obligation(ProofObligation::assert("mul_taut", "x * 2 == x * 2"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "200u8 * 2 must NOT verify — u8 multiplication overflow detected",
    );
}
