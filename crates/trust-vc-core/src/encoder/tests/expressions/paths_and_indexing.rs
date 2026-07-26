//! Multi-segment path (Type::MAX/MIN), negative literal width hints,
//! and bracket vs method-call index parity tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from expressions.rs (#2145).

use super::*;

// ========================================================================
// Multi-segment path tests (integer associated constants)
// ========================================================================

#[test]
fn test_i32_max_constant() {
    // i32::MAX == 2147483647
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == i32::MAX"));
    ctx.push_obligation(ProofObligation::assert("max_value", "x == 2147483647"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32::MAX should equal 2147483647");
}

#[test]
fn test_i32_min_constant() {
    // i32::MIN == -2147483648
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_min", "x == i32::MIN"));
    // -2147483648 is tricky as a literal, use comparison instead
    ctx.push_obligation(ProofObligation::assert("min_bound", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32::MIN should be negative");
}

#[test]
fn test_u32_max_constant() {
    // u32::MAX: all 32 bits set
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == u32::MAX"));
    // u32::MAX > 0 (unsigned)
    ctx.push_obligation(ProofObligation::assert("max_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32::MAX should be > 0 (unsigned)");
}

#[test]
fn test_u32_min_constant() {
    // u32::MIN == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_is_min", "x == u32::MIN"));
    ctx.push_obligation(ProofObligation::assert("min_is_zero", "x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32::MIN should equal 0");
}

#[test]
fn test_overflow_bound_check_with_max() {
    // Verify that x + 1 > x requires x < i32::MAX
    // When x == i32::MAX, x + 1 overflows (wraps), so x + 1 > x may not hold
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < i32::MAX"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x + 1 > x should verify when x < i32::MAX (no overflow)",
    );
}

#[test]
fn test_i32_max_overflow_counterexample() {
    // Without the x < i32::MAX bound, x + 1 > x can fail at MAX
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // No upper bound assumption — overflow can occur
    ctx.push_obligation(ProofObligation::assert("unsafe_increment", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x + 1 > x without bound should produce counterexample (overflow at MAX)",
    );
}

#[test]
fn test_i64_max_constant() {
    // i64::MAX bound check
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == i64::MAX"));
    ctx.push_obligation(ProofObligation::assert("max_positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i64::MAX should be positive");
}

#[test]
fn test_u8_max_constant() {
    // u8::MAX == 255
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == u8::MAX"));
    ctx.push_obligation(ProofObligation::assert("max_value", "x == 255"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8::MAX should equal 255");
}

#[test]
fn test_max_in_if_expression() {
    // Combine multi-segment path with if-else
    // if x > i32::MAX - 1 { 0 } else { x + 1 }
    // When x == 0, result should be 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "guarded_result",
        "if x == i32::MAX { 0 } else { x + 1 } == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Guarded increment with i32::MAX check should work");
}

// ========================================================================
// Negative literal width hint propagation (#1671)
// ========================================================================

#[test]
fn test_negative_literal_uses_context_width() {
    // Regression test for #1671: `-128` is parsed as Unary(Neg, Lit(128)).
    // The width hint must propagate through negation so the inner literal 128
    // uses the variable's BV width, not infer_int_width(). Without this fix,
    // the hint is lost and 128 may use a different width.
    //
    // Discriminating setup: declare more i32 vars than i8, so infer_int_width()
    // returns 32, but the comparison is against an i8 variable. The hint from
    // the i8 variable should override the heuristic for -128.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("min_val", "x == -128"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    // In i8: -128 is the minimum value. x == -128 should verify.
    // Without hint propagation through Neg: infer_int_width() = 32 (two i32 vars),
    // so 128 would become BV32(128), bvneg → BV32(-128). x is BV8 → width
    // mismatch at coerce_bv_widths, which extends x to BV32. The comparison
    // then depends on extension semantics, but with correct hint propagation,
    // 128 uses BV8(128), bvneg → BV8(-128), matching x's width directly.
    ctx.push_obligation(ProofObligation::assert("check_neg", "x == -128"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x == -128 with assumption x == -128 should verify in i8 context (even with i32 majority)",
    );
}

/// Discriminating regression test for #1671: verifies width hint propagation
/// through Unary(Neg) by exploiting BV wrapping at different widths.
///
/// Key insight: `0 + (-1)` wraps differently at BV8 vs BV32.
/// - BV8:  0 + (-1) = 255  (wraps at 2^8)
/// - BV32: 0 + (-1) = 4294967295 (wraps at 2^32)
///
/// Without the Neg hint fix, `-1` becomes BV32(-1) in i32-majority context.
/// The u8 variable `x` is zero-extended to BV32, and `BV32(0) + BV32(-1)`
/// yields BV32(4294967295), which != BV32(255). The assertion FAILS.
///
/// With the fix, `-1` gets hint (8, false) from the u8 variable, producing
/// BV8(-1) = BV8(255). `BV8(0) + BV8(255) = BV8(255)`. Assertion verifies.
#[test]
fn test_neg_hint_discriminates_via_unsigned_wrapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    // u8 wrapping: 0 + (-1) == 255. Only verifies if -1 is BV8, not BV32.
    ctx.push_obligation(ProofObligation::assert("wrap_check", "x + (-1) == 255"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u8 wrapping: 0 + (-1) should equal 255 in BV8 arithmetic",
    );
}

/// Discriminating regression test for #1648: u64 literal exceeding i64::MAX
/// must not be silently reinterpreted as a negative value.
///
/// 9223372036854775808 = i64::MAX + 1. Before the fix, `v as i64` cast this
/// to i64::MIN (-9223372036854775808), corrupting the BV constant.
/// With the fix (i128 parsing), the value is preserved correctly.
#[test]
fn test_u64_literal_exceeding_i64_max_not_sign_flipped() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 9223372036854775808"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u64 literal 9223372036854775808 (i64::MAX+1) should be positive",
    );
}

/// Truly discriminating regression test for #1648: u64::MAX literal in a
/// mixed-width context where infer_int_width returns 32.
///
/// Before fix: u64::MAX (18446744073709551615) was cast to i64 → -1.
/// With i32-majority variables, infer_int_width() returns 32.
/// fits_in_bv(-1, 32) → true (signed), so -1 got BV32(0xFFFFFFFF) = 4294967295.
/// Then x (u64) == BV32(4294967295) → sort mismatch or wrong value.
///
/// After fix: value = 18446744073709551615_i128, fits_in_bv(_, 32) → false
/// (exceeds unsigned 32-bit max). Widens appropriately. x == large_value
/// works correctly with matching widths.
#[test]
fn test_u64_max_literal_in_i32_majority_context() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    // Add i32 variables to create i32-majority context (infer_int_width → 32)
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0"));
    // u64::MAX. Before fix: -1 as i64 → BV32(0xFFFFFFFF) in i32-majority.
    // After fix: 18446744073709551615_i128 → doesn't fit BV32 → widens.
    ctx.push_obligation(ProofObligation::assume(
        "x_val",
        "x == 18446744073709551615",
    ));
    // x should be very large (u64::MAX), not 4294967295 (u32::MAX).
    // If sign-flipped to -1 and encoded as BV32, this would give wrong result.
    ctx.push_obligation(ProofObligation::assert("big_check", "x > 4294967296"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u64::MAX should be > 2^32 in u64 context. If BV32(-1) was used, value would be 4294967295 < 4294967296.");
}

// ========================================================================
// Bracket-syntax vs method-call index bounds check parity
// ========================================================================

/// Bracket-syntax `s[0]` on an empty Seq must NOT verify.
///
/// The IR pipeline (`prepare_context` -> `encode_condition_typed` ->
/// `encode_trust_vc_expr`) lowers `s[0]` to `TrustVcExpr::Index` which
/// goes through `indexing.rs:encode_index`, emitting a bounds check
/// (`0 <= idx < len`). This test verifies that the bounds check
/// correctly rejects the out-of-bounds access.
#[test]
fn test_bracket_index_on_empty_seq_emits_bounds_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert("bracket_index", "s[0] == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Bracket-syntax s[0] on empty seq should NOT verify (bounds check: 0 < 0 is false)",
    );
}

/// Method-call `s.index(0)` on an empty Seq must NOT verify.
///
/// Control test: verifies the method-call path also rejects the same
/// access, confirming parity between bracket-syntax and method-call paths.
#[test]
fn test_method_index_on_empty_seq_emits_bounds_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert("method_index", "s.index(0) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Method-call s.index(0) on empty seq should NOT verify (bounds check catches 0 < 0)",
    );
}

/// Bracket-syntax `s[0]` produces the correct element width for arithmetic.
///
/// After the #2180 fix, `Expr::Index` registers `element_width_info` in
/// `term_widths` so downstream operations (e.g., comparison with `i32::MAX`)
/// get the correct sort. Without width registration, `s[0] + 1` could fail
/// with a sort mismatch or silently produce wrong-width results.
#[test]
fn test_bracket_index_element_width_correct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() >= 1"));
    // s[0] should produce an i32-width term; comparing with 0 (i32 default)
    // exercises the width registration. If width is wrong, the assertion
    // would fail with a sort mismatch error rather than a clean result.
    ctx.push_obligation(ProofObligation::assert(
        "width_check",
        "s[0] >= 0 || s[0] < 0",
    ));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll's Seq theory disables model validation,
    // so the tautology (x >= 0 || x < 0) can't be model-validated and
    // the SAT result is demoted to Unknown. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_verified_or_unknown(
        &result,
        "#2680: native-seq model validation may prevent tautology confirmation",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_verified(
        &result,
        "Bracket-syntax s[0] should produce correct element width for arithmetic comparison",
    );
}
