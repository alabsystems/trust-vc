//! Overflow checks: assert_by scope (#1670), shift overflow (#1820),
//! and division/modulo by zero overflow (#1821).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from bitwise_and_overflow.rs (#2145).

use super::*;

// ========================================================================
// Overflow checks with assert_by scope (#1670)
// ========================================================================

/// DISCRIMINATING: overflow check should see assert_by-proven bounds.
///
/// Setup: x: i32 with only a lower bound assumption (x >= 0). The upper
/// bound (x < 2147483647) comes SOLELY from assert_by, proven via a
/// scoped assumption (x < 100).
///
/// Without fix #1670: overflow checker doesn't receive verified_assert_by,
/// so it sees only `x >= 0` — the solver finds x = 2147483647 where
/// x + 1 overflows signed i32, producing a false-positive overflow report.
///
/// With fix #1670: overflow checker sees `x < 2147483647` from
/// verified_assert_by, constraining x below overflow threshold.
#[test]
fn test_overflow_check_uses_assert_by_bounds() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Only a lower bound — no upper bound in regular assumptions
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    // assert_by proves an upper bound using a scoped proof.
    // The scoped assumption (x < 100) is available only during assert_by
    // verification; once proven, x < 2147483647 enters verified_assert_by.
    ctx.add_assert_by(
        "x_no_overflow",
        "x < 2147483647",
        vec![ProofObligation::assume("x_small", "x < 100")],
    );
    // This assertion triggers an overflow check for x + 1.
    // Without #1670: overflow checker has only x >= 0 — x could be
    // i32::MAX, so x + 1 overflows → false positive.
    // With #1670: overflow checker also has x < 2147483647 from
    // verified_assert_by → x + 1 cannot overflow.
    ctx.push_obligation(ProofObligation::assert("result_positive", "x + 1 > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x + 1 > 0 should verify — assert_by bound prevents overflow false positive",
    );
}

// ========================================================================
// Shift overflow checks (#1820)
// In Rust, shifting by >= bit width panics in debug / is UB in release.
// The encoder must generate overflow checks for Shl and Shr.
// ========================================================================

/// DISCRIMINATING: Left shift by a valid amount should verify.
/// 1u32 << 5 = 32, which is a valid shift.
#[test]
fn test_shl_valid_shift_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 5) == 32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "1u32 << 5 == 32 should verify with overflow checks",
    );
}

/// DISCRIMINATING: Left shift by >= bit width must NOT verify.
/// 1u32 << 32 is UB/panic in Rust. The overflow check should catch this.
#[test]
fn test_shl_overflow_shift_by_bitwidth_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "1u32 << 32 must NOT verify — shift amount >= bit width is overflow",
    );
}

/// DISCRIMINATING: Right shift by a valid amount should verify.
#[test]
fn test_shr_valid_shift_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 32"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 3) == 4"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "32u32 >> 3 == 4 should verify with overflow checks",
    );
}

/// DISCRIMINATING: Right shift by >= bit width must NOT verify.
#[test]
fn test_shr_overflow_shift_by_bitwidth_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "100u32 >> 32 must NOT verify — shift amount >= bit width is overflow",
    );
}

/// DISCRIMINATING: Variable shift amount that could overflow must NOT verify
/// without a bound constraint. Without overflow checks, (x << n) always produces
/// a BV result; with checks, the unconstrained n could be >= 32.
#[test]
fn test_shl_variable_shift_unbounded_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    // n is unconstrained — could be >= 32, triggering overflow check
    ctx.push_obligation(ProofObligation::assert("result", "(x << n) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x << n with unbounded n must NOT verify — overflow check fires",
    );
}

// ========================================================================
// Division/modulo by zero overflow checks (#1821)
// In Rust, division/modulo by zero panics. The encoder must generate
// overflow checks when the divisor is a non-literal expression.
// ========================================================================

/// DISCRIMINATING: Division by a proven-nonzero variable should verify.
/// x / y with y == 5 is safe; the div-by-zero check should pass.
#[test]
fn test_div_by_nonzero_variable_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == 20"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "100u32 / 5u32 == 20 should verify with overflow checks (#1821)",
    );
}

/// DISCRIMINATING: Division by an unconstrained variable must NOT verify.
/// y could be 0, so the div-by-zero overflow check should fire.
#[test]
fn test_div_by_unconstrained_variable_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    // y is unconstrained — could be 0
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x / y with unconstrained y must NOT verify — div-by-zero check fires (#1821)",
    );
}

/// DISCRIMINATING: Modulo by a proven-nonzero variable should verify.
#[test]
fn test_mod_by_nonzero_variable_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assert("mod_result", "x % y == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "17u32 %% 5u32 == 2 should verify with overflow checks (#1821)",
    );
}

/// DISCRIMINATING: Modulo by an unconstrained variable must NOT verify.
#[test]
fn test_mod_by_unconstrained_variable_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    // y is unconstrained — could be 0
    ctx.push_obligation(ProofObligation::assert("mod_result", "x % y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x %% y with unconstrained y must NOT verify — mod-by-zero check fires (#1821)",
    );
}

/// DISCRIMINATING: Division with requires(y != 0) precondition should verify.
/// This models the common Rust pattern where the caller ensures nonzero.
#[test]
fn test_div_with_nonzero_precondition_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == 20"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x / y with requires(y != 0) should verify (#1821)");
}

/// DISCRIMINATING: Modulo with requires(y != 0) precondition should verify.
/// Parity with test_div_with_nonzero_precondition_verifies.
#[test]
fn test_mod_with_nonzero_precondition_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assert("mod_result", "x % y == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x %% y with requires(y != 0) should verify (#1821)",
    );
}

/// DISCRIMINATING: Signed division by zero must be caught.
/// Exercises the bvsdiv path (signed BV division). Without the div-by-zero
/// check, bvsdiv(x, 0) has implementation-defined results in SMT-LIB.
///
/// Uses `x / y == x / y` (tautology) as the assertion so the test can
/// ONLY fail due to the overflow check on y, not due to the division
/// producing a negative result with a negative divisor. The original
/// assertion `x / y >= 0` was non-discriminating: it fails when y is
/// negative (e.g., 100 / -1 = -100 < 0) regardless of the div-by-zero check.
#[test]
fn test_signed_div_by_unconstrained_variable_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    // y is unconstrained signed — could be 0
    // Tautological assertion: only the overflow check (y != 0) can cause failure
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == x / y"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32 x / y with unconstrained y must NOT verify — div-by-zero check fires (#1821)",
    );
}

/// DISCRIMINATING: Signed modulo by zero must be caught.
/// Exercises the bvsrem path (signed BV remainder).
#[test]
fn test_signed_mod_by_unconstrained_variable_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    // y is unconstrained signed — could be 0
    ctx.push_obligation(ProofObligation::assert("mod_result", "x % y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32 x %% y with unconstrained y must NOT verify — mod-by-zero check fires (#1821)",
    );
}

/// DISCRIMINATING: Signed division with nonzero precondition should verify.
/// Tests that the signed path (bvsdiv) works correctly when the divisor is
/// proven nonzero.
#[test]
fn test_signed_div_with_nonzero_precondition_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("nonzero", "y != 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y == 20"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i32 x / y with requires(y != 0) should verify (#1821)",
    );
}

/// DISCRIMINATING: Divisor range includes zero (y >= 0) must NOT verify.
/// Even though y is non-negative, y == 0 is possible and must be caught.
/// This tests the boundary: a "mostly safe" range that still includes zero.
#[test]
fn test_div_by_nonnegative_variable_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_nonneg", "y >= 0"));
    // y >= 0 for u32 is always true, but y could still be 0
    ctx.push_obligation(ProofObligation::assert("div_result", "x / y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x / y with y >= 0 (includes zero!) must NOT verify (#1821)",
    );
}

/// DISCRIMINATING: Divisor constrained to y > 0 (strictly positive) should verify.
/// This tests that y > 0 is sufficient (unlike y >= 0 which includes zero).
#[test]
fn test_div_by_strictly_positive_variable_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("y_pos", "y > 0"));
    ctx.push_obligation(ProofObligation::assume("y_small", "y <= 100"));
    ctx.push_obligation(ProofObligation::assert("div_nonneg", "x / y >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x / y with y > 0 should verify — strictly positive excludes zero (#1821)",
    );
}
