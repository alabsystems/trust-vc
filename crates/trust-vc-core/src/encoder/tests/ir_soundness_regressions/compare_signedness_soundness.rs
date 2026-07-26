// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comparison encoding signedness soundness tests.
//!
//! Tests that the signed/unsigned dispatch in compare.rs produces correct
//! results for boundary cases. If the comparison encoding uses the wrong
//! signedness, these tests will fail — they are *discriminating*, meaning
//! incorrect encoding cannot accidentally produce the correct answer.
//!
//! Key invariants tested:
//! - Signed comparisons (`i32`, `i64`) use `bvslt`/`bvsle`/etc.
//! - Unsigned comparisons (`u32`, `u64`) use `bvult`/`bvule`/etc.
//! - Mixed comparisons default to signed (AND semantics, #1769)
//! - Constant-expression comparisons use Int semantics, not BV wrapping (#2668)

use super::*;

// ========================================================================
// Signed comparison soundness: negative values
// ========================================================================

/// DISCRIMINATING: -1i32 < 0i32 must verify.
/// If unsigned comparison were used, -1 wraps to u32::MAX (4294967295),
/// and 4294967295 < 0 is false → the test would fail.
#[test]
fn test_signed_compare_negative_one_less_than_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_neg1", "x == -1i32"));
    ctx.push_obligation(ProofObligation::assert("neg_lt_zero", "x < 0i32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "-1i32 < 0i32 must verify (signed comparison): if unsigned were used, -1 wraps to MAX",
    );
}

/// DISCRIMINATING: negative value must NOT be greater than positive.
/// If unsigned were used, -1 wraps to MAX which IS greater than 1.
#[test]
fn test_signed_compare_negative_not_greater_than_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_neg1", "x == -1i32"));
    ctx.push_obligation(ProofObligation::assert("neg_gt_pos", "x > 1i32"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "-1i32 > 1i32 must NOT verify: if unsigned were used, it would (MAX > 1)",
    );
}

// ========================================================================
// Unsigned comparison soundness: wrapping behavior
// ========================================================================

/// DISCRIMINATING: u32::MAX > 0u32 must verify.
/// This is trivially true for unsigned but could fail if signed comparison
/// were used (u32::MAX = -1 in signed, and -1 > 0 is false in signed).
#[test]
fn test_unsigned_compare_max_greater_than_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_max", "x == 4294967295u32"));
    ctx.push_obligation(ProofObligation::assert("max_gt_zero", "x > 0u32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32::MAX > 0u32 must verify (unsigned comparison): \
         if signed were used, MAX = -1 and -1 > 0 is false",
    );
}

/// DISCRIMINATING: for unsigned, large values must NOT be less than small.
/// u32::MAX < 1u32 must NOT verify.
#[test]
fn test_unsigned_compare_max_not_less_than_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_max", "x == 4294967295u32"));
    ctx.push_obligation(ProofObligation::assert("max_lt_one", "x < 1u32"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32::MAX < 1u32 must NOT verify (unsigned comparison)",
    );
}

// ========================================================================
// Signed i8 boundary: two's complement corner case
// ========================================================================

/// DISCRIMINATING: i8::MIN (-128) < i8::MAX (127) must verify.
/// If unsigned were used: 128 < 127 is false.
#[test]
fn test_signed_i8_min_less_than_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -128i8"));
    ctx.push_obligation(ProofObligation::assume("y_max", "y == 127i8"));
    ctx.push_obligation(ProofObligation::assert("min_lt_max", "x < y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i8::MIN < i8::MAX must verify: -128 < 127 in signed, 128 < 127 in unsigned (WRONG)",
    );
}

// ========================================================================
// Mixed signedness: i32 vs u32 uses signed semantics (AND rule #1769)
// ========================================================================

/// DISCRIMINATING: mixed-sign comparison should NOT treat -1 as u32::MAX.
/// When comparing i32 with u32, the AND rule (#1769) requires BOTH sides
/// to be unsigned for unsigned comparison. One signed operand forces signed.
#[test]
fn test_mixed_sign_comparison_uses_signed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_neg1", "x == -1i32"));
    // Compare x (i32, signed) against an unsigned literal 0u32.
    // Under AND semantics: signed(i32) AND unsigned(u32) = signed.
    // So -1 < 0 is true in signed.
    // If unsigned were incorrectly chosen: 4294967295 < 0 = false.
    ctx.push_obligation(ProofObligation::assert("mixed_lt", "x < 0u32"));

    let result = AYEncoder::verify(&ctx);
    // Note: this comparison goes through literal coercion in ir_lowering,
    // which coerces the 0u32 literal peer-type to match the signed x.
    // The result should verify because -1 < 0 is true in signed semantics.
    expect_verified(
        &result,
        "i32 vs u32 comparison must use signed semantics (AND rule #1769): \
         -1i32 < 0u32 → -1 < 0 in signed = true",
    );
}

// ========================================================================
// Constant-expression BV-compare guard (#2668)
// ========================================================================

/// Constant expressions should NOT be BV-wrapped when use_int_arithmetic is active.
/// The `is_definitely_var_free_for_bv_compare` guard prevents BV compare
/// on fully-constant post-substitution expressions.
///
/// 1 + 1 == 2 is trivially true in Int semantics.
/// In BV(32) semantics it's also true, but large constants could wrap.
/// The test uses a value near the boundary to detect wrapping.
#[test]
fn test_constant_compare_uses_int_not_bv() {
    // 2147483647 + 1 == 2147483648 is true in Int semantics
    // but wraps to -2147483648 in BV(32) signed, making it != 2147483648.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "x + 1 == 2147483648"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MathInt 2147483647 + 1 == 2147483648 must verify: \
         if BV(32) wrapping were applied, 2147483647 + 1 = -2147483648 (WRONG)",
    );
}

// ========================================================================
// Equality comparison: must not be affected by signedness
// ========================================================================

/// Equality comparison should NOT care about signedness.
/// Both signed and unsigned Eq/Ne should use `try_eq` (term equality).
#[test]
fn test_equality_not_affected_by_signedness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_val", "x == 42u32"));
    ctx.push_obligation(ProofObligation::assert("eq_42", "x == 42u32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 == u32 equality must verify");
}

/// DISCRIMINATING: inequality should detect difference.
#[test]
fn test_inequality_detects_difference() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_val", "x == 42i32"));
    ctx.push_obligation(ProofObligation::assert("ne_43", "x != 43i32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42i32 != 43i32 must verify");
}

/// DISCRIMINATING: inequality must fail when values are equal.
#[test]
fn test_inequality_fails_when_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("is_val", "x == 42i32"));
    ctx.push_obligation(ProofObligation::assert("ne_42", "x != 42i32"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "42i32 != 42i32 must NOT verify");
}

/// DISCRIMINATING: native-seq `s.len() > x` must use signed BV-to-Int coercion
/// when `x: i32`. If the fallback uses unsigned `bv2int`, `-1i32` becomes
/// `4294967295`, making `0 > x` spuriously false.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_len_compare_signed_negative_uses_signed_coercion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("len_zero", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assume("neg_one", "x == -1i32"));
    ctx.push_obligation(ProofObligation::assert("len_gt_neg", "s.len() > x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native-seq len compare against -1i32 must verify using signed BV-to-Int coercion",
    );
}

/// DISCRIMINATING: native-seq `s.len() > -1i32` must keep the negated literal
/// on the Int-sorted path. This exercises the direct `encode_neg` literal case
/// from #2700 instead of routing through an intermediate variable binding.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_len_compare_direct_negative_literal_uses_math_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_zero", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "len_gt_neg_literal",
        "s.len() > -1i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native-seq len compare against direct -1i32 literal must verify without BV negation",
    );
}

/// DISCRIMINATING: the same signed coercion must also reject the inverted
/// comparison. Unsigned `bv2int` would reinterpret `-1i32` as a large
/// positive integer and could accidentally satisfy `s.len() < x`.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_len_compare_signed_negative_rejects_inverted_compare() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("len_zero", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assume("neg_one", "x == -1i32"));
    ctx.push_obligation(ProofObligation::assert("len_lt_neg", "s.len() < x"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native-seq len compare against -1i32 must NOT verify the inverted ordering",
    );
}

/// DISCRIMINATING: the direct negative literal case must also reject the
/// inverted ordering. If `encode_neg` regresses back to BV-only handling for
/// the promoted Int term, this can fail with an encoder error or spuriously
/// satisfy the comparison under unsigned reinterpretation.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_len_compare_direct_negative_literal_rejects_inverted_compare() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_zero", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "len_lt_neg_literal",
        "s.len() < -1i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native-seq len compare against direct -1i32 literal must NOT verify the inverted ordering",
    );
}
