//! Signed overflow both-direction tests (#1835), right shift signedness
//! tests (#1841), and signed MIN/-1 overflow checks (#1873).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from bitwise_and_overflow.rs (#2145).

use super::*;

// ========================================================================
// Signed overflow both-direction tests (#1835)
// TrustVc must check BOTH overflow (pos+pos=>neg) AND underflow (neg+neg=>pos)
// for signed addition/subtraction. If only one direction is checked, the
// other can produce silently wrong results (cf. ay_bindings ay#3916).
// ========================================================================

/// DISCRIMINATING: Signed addition positive overflow must be caught.
/// i32::MAX + 1 overflows to i32::MIN — the overflow check must fire.
#[test]
fn test_signed_add_positive_overflow_caught() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 2147483647")); // i32::MAX
    ctx.push_obligation(ProofObligation::assume("y_one", "y == 1"));
    // x + y overflows: 2147483647 + 1 wraps to -2147483648
    ctx.push_obligation(ProofObligation::assert("sum_positive", "x + y > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MAX + 1 must NOT verify — positive overflow should be caught (#1835)",
    );
}

/// DISCRIMINATING: Signed addition negative underflow must be caught.
/// i32::MIN + (-1) underflows to i32::MAX — the underflow check must fire.
/// This is the exact case that ay_bindings misses (ay#3916).
#[test]
fn test_signed_add_negative_underflow_caught() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648")); // i32::MIN
    ctx.push_obligation(ProofObligation::assume("y_neg", "y == -1"));
    // x + y underflows: -2147483648 + (-1) wraps to 2147483647
    ctx.push_obligation(ProofObligation::assert("sum_negative", "x + y < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MIN + (-1) must NOT verify — negative underflow should be caught (#1835)",
    );
}

/// DISCRIMINATING: Safe signed addition within range should verify.
/// 100 + 200 = 300, well within i32 range.
#[test]
fn test_signed_add_no_overflow_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 200"));
    ctx.push_obligation(ProofObligation::assert("sum_correct", "x + y == 300"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "100 + 200 == 300 should verify (no overflow) (#1835)",
    );
}

/// DISCRIMINATING: Signed subtraction underflow must be caught.
/// i32::MIN - 1 underflows.
#[test]
fn test_signed_sub_underflow_caught() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648")); // i32::MIN
    ctx.push_obligation(ProofObligation::assume("y_one", "y == 1"));
    // x - y underflows: -2147483648 - 1 wraps
    ctx.push_obligation(ProofObligation::assert("diff_negative", "x - y < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MIN - 1 must NOT verify — subtraction underflow should be caught (#1835)",
    );
}

// ========================================================================
// Right shift signedness tests (#1841)
// Rust >> uses logical shift for unsigned types (bvlshr) and arithmetic
// shift for signed types (bvashr). When the shift amount is a literal,
// the literal defaults to signed, causing operands_are_unsigned to return
// false even for unsigned left operands. The fix uses only the left
// operand's signedness for right shift.
// ========================================================================

/// DISCRIMINATING: u32 >> 1 on a value with high bit set must use logical shift.
/// 0x8000_0000u32 >> 1 = 0x4000_0000 (logical), not 0xC000_0000 (arithmetic).
/// Before #1841 fix, bvashr was used, producing 0xC000_0000.
#[test]
fn test_unsigned_right_shift_literal_uses_logical() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483648")); // 0x8000_0000
                                                                              // Logical: 0x8000_0000 >> 1 = 0x4000_0000 = 1073741824
    ctx.push_obligation(ProofObligation::assert(
        "shr_result",
        "x >> 1 == 1073741824",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32(0x8000_0000) >> 1 should be 0x4000_0000 (logical shift)",
    );
}

/// DISCRIMINATING: u32 >> 1 must NOT produce the arithmetic shift result.
/// If bvashr is used, 0x8000_0000 >> 1 = 0xC000_0000 = 3221225472.
/// This must NOT verify (it would only verify with bvashr, not bvlshr).
#[test]
fn test_unsigned_right_shift_not_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483648")); // 0x8000_0000
                                                                              // Arithmetic: 0x8000_0000 >> 1 = 0xC000_0000 = 3221225472
    ctx.push_obligation(ProofObligation::assert("shr_arith", "x >> 1 == 3221225472"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32(0x8000_0000) >> 1 must NOT be 0xC000_0000 (that's arithmetic shift)",
    );
}

/// CONTROL: i32 >> 1 on a negative value must still use arithmetic shift.
/// -2 (0xFFFFFFFE) >> 1 = -1 (0xFFFFFFFF) with arithmetic shift.
/// This verifies that the fix didn't break signed right shift.
#[test]
fn test_signed_right_shift_still_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -2"));
    // Arithmetic: -2 >> 1 = -1 (sign-extends the MSB)
    ctx.push_obligation(ProofObligation::assert("shr_signed", "x >> 1 == -1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32(-2) >> 1 should be -1 (arithmetic shift)");
}

// ========================================================================
// Signed MIN / -1 overflow checks (#1873)
// In Rust, i32::MIN / -1 and i32::MIN % -1 panic because the quotient
// overflows the signed range. The encoder must generate overflow checks
// for both BV-mode and Int-mode division/remainder.
// ========================================================================

/// DISCRIMINATING: BV-mode i32::MIN / -1 must NOT verify.
/// The quotient 2147483648 overflows i32, causing a panic in Rust.
#[test]
fn test_bv_signed_div_min_by_neg1_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648")); // i32::MIN
    ctx.push_obligation(ProofObligation::assume("y_neg1", "y == -1"));
    // Tautological assertion: only the overflow check can cause failure
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == x / y"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MIN / -1 must NOT verify — signed division overflow (#1873)",
    );
}

/// DISCRIMINATING: BV-mode i32::MIN % -1 must NOT verify.
/// The intermediate quotient overflows, making the remainder undefined.
#[test]
fn test_bv_signed_rem_min_by_neg1_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648")); // i32::MIN
    ctx.push_obligation(ProofObligation::assume("y_neg1", "y == -1"));
    // Tautological assertion: only the overflow check can cause failure
    ctx.push_obligation(ProofObligation::assert("rem_result", "x % y == x % y"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MIN %% -1 must NOT verify — signed remainder overflow (#1873)",
    );
}

/// CONTROL: BV-mode signed division by -1 on non-MIN values should verify.
/// -100 / -1 == 100, which is safe.
#[test]
fn test_bv_signed_div_non_min_by_neg1_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -100"));
    ctx.push_obligation(ProofObligation::assume("y_neg1", "y == -1"));
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "-100 / -1 == 100 should verify — no overflow (#1873)",
    );
}

/// CONTROL: BV-mode signed remainder by -1 on non-MIN values should verify.
/// -100 % -1 == 0, which is safe.
#[test]
fn test_bv_signed_rem_non_min_by_neg1_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -100"));
    ctx.push_obligation(ProofObligation::assume("y_neg1", "y == -1"));
    ctx.push_obligation(ProofObligation::assert("rem_result", "x % y == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "-100 %% -1 == 0 should verify — no overflow (#1873)",
    );
}

/// DISCRIMINATING: Unconstrained signed division must catch MIN/-1 overflow.
/// When x and y are unconstrained i32, the solver can find x=MIN, y=-1.
#[test]
fn test_bv_signed_div_unconstrained_catches_min_neg1() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    // Tautological assertion: only overflow checks can cause failure
    ctx.push_obligation(ProofObligation::assert("div_taut", "x / y == x / y"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Unconstrained i32 x / y (y != 0) must NOT verify — MIN/-1 overflow (#1873)",
    );
}

/// DISCRIMINATING: Unconstrained signed remainder must catch MIN/-1 overflow.
#[test]
fn test_bv_signed_rem_unconstrained_catches_min_neg1() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    // Tautological assertion: only overflow checks can cause failure
    ctx.push_obligation(ProofObligation::assert("rem_taut", "x % y == x % y"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Unconstrained i32 x %% y (y != 0) must NOT verify — MIN/-1 overflow (#1873)",
    );
}

/// CONTROL: Signed division with both nonzero and no-MIN/-1 preconditions should verify.
#[test]
fn test_bv_signed_div_with_full_preconditions_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    ctx.push_obligation(ProofObligation::assume(
        "not_min_neg1",
        "!(x == -2147483648 && y == -1)",
    ));
    // With both preconditions, tautological assertion should verify
    ctx.push_obligation(ProofObligation::assert("div_taut", "x / y == x / y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i32 x / y with y != 0 and !(MIN, -1) should verify (#1873)",
    );
}

/// CONTROL: Unsigned division has no MIN/-1 issue.
/// u32 has no negative values, so MIN/-1 overflow cannot occur.
#[test]
fn test_bv_unsigned_div_no_min_neg1_issue() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y > 0"));
    ctx.push_obligation(ProofObligation::assert("div_nonneg", "x / y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 x / y with y > 0 should verify — no MIN/-1 issue for unsigned (#1873)",
    );
}

// Wrapping and checked arithmetic tests moved to wrapping_and_checked.rs (P1-214)
