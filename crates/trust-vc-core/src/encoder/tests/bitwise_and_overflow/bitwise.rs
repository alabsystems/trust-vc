//! Bitwise operation tests (#1566) and saturating arithmetic regression
//! tests (#1685).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from bitwise_and_overflow.rs (#2145).

use super::*;

// ========================================================================
// Bitwise operation tests (Issue #1566)
// ========================================================================

#[test]
fn test_boolean_not_on_bool_expression() {
    // !true should be boolean NOT (verified via simple negation)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("pos", "x > 0"));
    // !(x > 0) should be false when x > 0
    ctx.push_obligation(ProofObligation::assert("neg_pos", "!(x > 0)"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "!(x > 0) should be a counterexample when x > 0");
}

#[test]
fn test_bitwise_and_operator() {
    // x & 0 == 0 should always hold (bitwise AND with 0)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("and_zero", "x & 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x & 0 == 0 should be verified for all x");
}

#[test]
fn test_bitwise_or_operator() {
    // x | 0 == x should always hold (bitwise OR with 0)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("or_zero", "x | 0 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x | 0 == x should be verified for all x");
}

#[test]
fn test_bitwise_xor_self_is_zero() {
    // x ^ x == 0 should always hold
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("xor_self", "x ^ x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x ^ x == 0 should be verified for all x");
}

#[test]
fn test_bitwise_not_on_integer() {
    // For bitvectors: !0 == -1 (all bits set).
    // In 32-bit two's complement, !0i32 == -1i32 == 0xFFFFFFFF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("is_zero", "x == 0"));
    // !x should be -1 (all bits flipped)
    ctx.push_obligation(ProofObligation::assert("not_zero_is_minus_one", "!x == -1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!0i32 == -1 should be verified (bitwise NOT)");
}

#[test]
fn test_shift_left_operator() {
    // 1 << 3 == 8
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("is_one", "x == 1"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("is_three", "y == 3"));
    ctx.push_obligation(ProofObligation::assert("shl", "x << y == 8"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 3 == 8 should be verified");
}

#[test]
fn test_shift_right_operator() {
    // 8 >> 3 == 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("is_eight", "x == 8"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("is_three", "y == 3"));
    ctx.push_obligation(ProofObligation::assert("shr", "x >> y == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8 >> 3 == 1 should be verified");
}

#[test]
fn test_bitwise_not_on_arithmetic_result() {
    // !(x + y) where x, y are i32 — the arithmetic result is a BV term
    // NOT tracked in term_widths. The ! operator must still use bvnot.
    // If x == 0 and y == 0, then !(x+y) == !0 == -1 (all bits set).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_zero", "y == 0"));
    ctx.push_obligation(ProofObligation::assert("not_sum", "!(x + y) == -1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "!(0 + 0) should be -1 (bitwise NOT on arithmetic result)",
    );
}

#[test]
fn test_bitwise_not_u8() {
    // !0xFF_u8 should equal 0x00_u8 (bitwise NOT on 8-bit unsigned)
    // Acceptance criterion #3 from #1566
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("is_ff", "x == 255"));
    // Bitwise NOT of 0xFF (255) should be 0x00 (0)
    ctx.push_obligation(ProofObligation::assert("not_ff_is_zero", "!x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!0xFF_u8 should equal 0x00_u8 (bitwise NOT)");
}

#[test]
fn test_bitwise_not_u8_inverse() {
    // Negative test: !0x00_u8 should NOT equal 0x00_u8
    // (it should be 0xFF = 255)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("is_zero", "x == 0"));
    // !0 for u8 should be 255, so asserting == 0 must fail
    ctx.push_obligation(ProofObligation::assert("not_zero_is_zero", "!x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "!0x00_u8 should NOT equal 0x00_u8 (should be 0xFF)",
    );
}

// ========================================================================
// Saturating arithmetic with i64 — regression tests for #1685
// ========================================================================

/// DISCRIMINATING: i64 saturating_add must not panic when computing type bounds.
///
/// Before fix: `(1i64 << 63) - 1` in methods.rs:240 panics in debug mode
/// because `1i64 << 63` produces `i64::MIN`, and `i64::MIN - 1` overflows.
/// After fix: BigInt arithmetic avoids i64 overflow entirely.
///
/// This test declares x as i64 (width=64), which forces the saturating_add
/// code path through the signed bounds computation. If it doesn't panic,
/// the BigInt fix is working.
#[test]
fn test_saturating_add_i64_no_panic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume(
        "x_is_max",
        "x == 9223372036854775807",
    )); // i64::MAX
        // i64::MAX.saturating_add(1) should equal i64::MAX (saturation)
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_max",
        "x.saturating_add(1) == 9223372036854775807",
    ));

    let result = AYEncoder::verify(&ctx);
    // The old code would panic before reaching this assertion.
    // With the #1685 fix, saturating_add encodes correctly and verifies.
    expect_verified(
        &result,
        "saturating_add on i64 must not produce an error (was panic before #1685 fix)",
    );
}

/// DISCRIMINATING: i64 saturating_sub underflow should not panic.
///
/// Same root cause as saturating_add: the signed MIN computation
/// `-(1i64 << 63)` panics when width == 64 because `1i64 << 63`
/// is `i64::MIN` and negating `i64::MIN` overflows.
#[test]
fn test_saturating_sub_i64_no_panic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume(
        "x_is_min",
        "x == -9223372036854775808",
    )); // i64::MIN
        // i64::MIN.saturating_sub(1) should equal i64::MIN (saturation)
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_min",
        "x.saturating_sub(1) == -9223372036854775808",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "saturating_sub on i64 must not produce an error (was panic before #1685 fix)",
    );
}
