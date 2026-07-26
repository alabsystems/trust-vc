//! Division, width coercion, and sign-extension tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from expressions.rs (#2145).

use super::*;

// ========================================================================
// Division by zero detection tests (Issue #59)
// ========================================================================

#[test]
fn test_division_by_constant_zero_rejected() {
    // "x / 0" should be rejected at parse time
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("div_zero", "x / 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Division by zero"),
                "Error should mention division by zero: {}",
                message
            );
        }
        _ => panic!("Expected Error for division by zero, got: {:?}", result),
    }
}

#[test]
fn test_modulo_by_constant_zero_rejected() {
    // "x % 0" should be rejected at parse time
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("mod_zero", "x % 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Modulo by zero"),
                "Error should mention modulo by zero: {}",
                message
            );
        }
        _ => panic!("Expected Error for modulo by zero, got: {:?}", result),
    }
}

// ========================================================================
// Integer division tests (Issue #80)
// ========================================================================

#[test]
fn test_integer_division_in_expression() {
    // Issue #80: division on Int types should use int_div, not div
    // This test ensures integer division doesn't panic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("div_test", "x / 2 >= 0"));

    // This should not panic and should encode without errors
    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(
        &result,
        "integer division (issue #80) should not produce encoder errors",
    );
}

#[test]
fn test_integer_division_with_constants() {
    // Test division with constant operands
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_div", "10 / 3 == 3")); // Integer division: 10/3 = 3

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 / 3 should equal 3 in integer division");
}

#[test]
fn test_integer_division_rounding() {
    // Integer division truncates toward zero
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("truncate", "7 / 2 == 3")); // 7/2 = 3 (truncated)

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 / 2 should equal 3 (truncated)");
}

// ========================================================================
// Width coercion tests (Issue #1104)
// ========================================================================

#[test]
fn test_mixed_width_comparison_i32_vs_i64() {
    // When comparing i32 and i64 variables, the i32 should be sign-extended
    // to 64-bit before comparison so the ay sorts match.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("small", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("big", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume("small_val", "small == 5"));
    ctx.push_obligation(ProofObligation::assume("big_val", "big == 10"));
    ctx.push_obligation(ProofObligation::assert("compare", "small < big"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i32(5) < i64(10) should verify with width coercion",
    );
}

#[test]
fn test_mixed_width_arithmetic_i16_plus_i32() {
    // i16 + i32 should extend i16 to 32-bit before adding
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert("sum", "a + b == 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i16(3) + i32(7) should equal 10 with width coercion",
    );
}

#[test]
fn test_same_width_no_coercion_needed() {
    // Same-width operations should still work (regression test)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 20"));
    ctx.push_obligation(ProofObligation::assert("sum", "x + y == 30"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32 + i32 should verify without coercion");
}

// ========================================================================
// Sign-extension correctness tests (Issue #1510)
// ========================================================================

#[test]
fn test_sign_extension_unsigned_boundary() {
    // Regression test for #1510: coerce_bv_widths must use zero-extension
    // for unsigned types. u8(200) = 0xC8 zero-extended to 32 bits must be
    // 0x000000C8 (200), not 0xFFFFFFC8 (-56 via sign-extension).
    // Fixed in [W1]99 — this test must pass (assert Verified).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("small", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("big", crate::ir::TrustVcType::parse_or_opaque("u32"));

    // small == 200 (high bit set in u8)
    ctx.push_obligation(ProofObligation::assume("small_val", "small == 200"));
    // big == 200
    ctx.push_obligation(ProofObligation::assume("big_val", "big == 200"));
    // After correct zero-extension, small should equal big
    ctx.push_obligation(ProofObligation::assert(
        "equal_after_promotion",
        "small == big",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u8(200) zero-extended to u32 should equal u32(200)",
    );
}

#[test]
fn test_mixed_signedness_comparison_independence() {
    // Regression test for #1516: per-expression signedness ensures signed
    // comparisons use signed semantics even when unsigned variables exist
    // in the same context.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signed_val", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed(
        "unsigned_val",
        crate::ir::TrustVcType::parse_or_opaque("u32"),
    );

    // signed_val == -1 (valid for i32)
    ctx.push_obligation(ProofObligation::assume("signed_neg", "signed_val == -1"));
    // signed_val < 0 should be true: with per-expression signedness,
    // this uses bvslt (signed) because signed_val is i32.
    ctx.push_obligation(ProofObligation::assert("neg_is_negative", "signed_val < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Signed comparison in mixed context should use signed semantics",
    );
}

#[test]
fn test_u64_max_literal_does_not_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    // u64::MAX = 18446744073709551615
    // As a 64-bit bitvec, this is all 1s, equivalent to -1 in i64
    ctx.push_obligation(ProofObligation::assume(
        "max_val",
        "x == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "x == 18446744073709551615",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x == u64::MAX with assumption x == u64::MAX should verify",
    );
}
