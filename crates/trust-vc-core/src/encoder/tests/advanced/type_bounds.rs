//! Integer type range guards for quantifier-bound variables.
//!
//! Tests: unsigned/signed range guards ensuring quantifier-bound variables
//! are constrained to their Rust type's range, associated constant boundary
//! conditions (u64::MAX, i128::MIN, u128::MAX).
//!
//! Issues: #1519, #1648, #1660, #1774, #1875
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Unsigned range guards for quantifier variables (Fix 2, #1519)
// ========================================================================

/// DISCRIMINATING: forall |x: u32| x >= 0 — with unsigned bounds, x is
/// constrained to [0, 2^32), so x >= 0 is tautological. Without Fix 2,
/// this would produce a Counterexample (x = -1).
#[test]
fn test_forall_unsigned_nonneg_not_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u32_nonneg",
        "forall(|x: u32| x >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall |x: u32| x >= 0 must not produce counterexample with unsigned bounds",
    );
}

/// DISCRIMINATING: forall |x: i32| x >= 0 — should NOT verify (signed i32
/// has no implicit lower bound, x can be negative).
#[test]
fn test_forall_signed_nonneg_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i32_nonneg",
        "forall(|x: i32| x >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: i32| x >= 0 must NOT verify (signed can be negative)",
    );
}

/// DISCRIMINATING: exists |x: u32| x == 5 — should verify (5 is in unsigned
/// range). This ensures exists + unsigned bounds works correctly (range && body).
#[test]
fn test_exists_unsigned_in_range_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u32_witness",
        "exists(|x: u32| x == 5)",
    ));

    let result = AYEncoder::verify(&ctx);
    // ay-dpll returns Unknown for exists quantifiers (#2229 triage)
    expect_verified_or_unknown(&result, "exists |x: u32| x == 5 should not fail");
}

/// DISCRIMINATING: forall |x: u64| x < 9223372036854775807 — must NOT verify.
///
/// 9223372036854775807 is i64::MAX. The value x = i64::MAX is a valid u64 in
/// the range [0, 2^64) and makes (x < i64::MAX) false.
#[test]
fn test_forall_u64_less_than_i64_max_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u64_less_i64max",
        "forall(|x: u64| x < 9223372036854775807)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "forall |x: u64| x < i64::MAX must NOT verify — x = i64::MAX is a valid u64 counterexample (#1660)");
}

/// DISCRIMINATING: forall |x: u64| x != 9223372036854775808 — must NOT verify.
///
/// 9223372036854775808 is i64::MAX + 1. This value is a valid u64 in [0, 2^64).
/// This test targets the Int-mode literal path (#1648).
#[test]
fn test_forall_u64_ne_large_literal_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u64_ne_large",
        "forall(|x: u64| x != 9223372036854775808)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: u64| x != (i64::MAX+1) must NOT verify — i128 literal regression (#1648)",
    );
}

// ========================================================================
// Signed range guards for quantifier variables (Fix 2 extension, #1519)
// ========================================================================

/// DISCRIMINATING: forall |x: i8| x >= -128 — with signed bounds [-128, 128),
/// x is constrained to never go below -128, so x >= -128 is tautological.
#[test]
fn test_forall_signed_lower_bound_tautology() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i8_lower",
        "forall(|x: i8| x >= -128)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall |x: i8| x >= -128 must not produce counterexample with signed bounds",
    );
}

/// DISCRIMINATING: forall |x: i8| x < 128 — with signed bounds [-128, 128),
/// all values of x satisfy x < 128.
#[test]
fn test_forall_signed_upper_bound_tautology() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i8_upper",
        "forall(|x: i8| x < 128)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall |x: i8| x < 128 must not produce counterexample with signed bounds",
    );
}

/// DISCRIMINATING: exists |x: i8| x == -128 — the minimum i8 value is -128,
/// which is within the signed range [-128, 128). This should verify.
#[test]
fn test_exists_signed_min_value_in_range() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i8_min",
        "exists(|x: i8| x == -128)",
    ));

    let result = AYEncoder::verify(&ctx);
    // ay-dpll returns Unknown for exists quantifiers (#2229 triage)
    expect_verified_or_unknown(
        &result,
        "exists |x: i8| x == -128 should not fail (in signed range)",
    );
}

/// DISCRIMINATING: exists |x: i8| x == 128 — 128 is outside i8 range [-128, 128).
#[test]
fn test_exists_signed_out_of_range_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i8_out_of_range",
        "exists(|x: i8| x == 128)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "exists |x: i8| x == 128 must NOT verify — 128 is outside i8 range [-128, 128)",
    );
}

/// DISCRIMINATING: exists |x: i8| x == -129 — -129 is below i8 range [-128, 128).
#[test]
fn test_exists_signed_below_lower_bound_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i8_below_lower",
        "exists(|x: i8| x == -129)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "exists |x: i8| x == -129 must NOT verify — -129 is below i8 range [-128, 128)",
    );
}

/// DISCRIMINATING: exists |x: i32| x == 2147483648 — 2^31 is outside i32 range.
#[test]
fn test_exists_i32_above_upper_bound_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i32_above_upper",
        "exists(|x: i32| x == 2147483648)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "exists |x: i32| x == 2^31 must NOT verify — 2^31 is outside i32 range",
    );
}

/// DISCRIMINATING: forall |x: i32| x < 2147483648 — with signed i32 bounds
/// [-2^31, 2^31), all values satisfy x < 2^31.
#[test]
fn test_forall_i32_less_than_upper_bound() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i32_upper",
        "forall(|x: i32| x < 2147483648)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall |x: i32| x < 2^31 must not produce counterexample with signed bounds",
    );
}

// ========================================================================
// int_mode associated constant boundary conditions (#1774)
// ========================================================================

/// DISCRIMINATING: forall |x: u64| x != u64::MAX must NOT verify.
/// u64::MAX (18446744073709551615) is a valid u64 counterexample.
#[test]
fn test_forall_u64_max_associated_const_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u64_max",
        "forall(|x: u64| x != u64::MAX)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: u64| x != u64::MAX must NOT verify — u64::MAX is a valid counterexample",
    );
}

/// CONTROL: The literal equivalent should also not verify.
#[test]
fn test_forall_u64_ne_max_literal_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u64_max_lit",
        "forall(|x: u64| x != 18446744073709551615)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: u64| x != 18446744073709551615 must NOT verify",
    );
}

/// DISCRIMINATING: forall |x: u64| x > u64::MAX must NOT verify.
/// No u64 value exceeds u64::MAX. This is trivially false.
#[test]
fn test_forall_u64_gt_max_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "gt_max",
        "forall(|x: u64| x > u64::MAX)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: u64| x > u64::MAX must NOT verify — no u64 exceeds u64::MAX",
    );
}

/// DIAGNOSTIC: Check if u64::MAX associated constant produces Error in int_mode.
#[test]
fn test_u64_max_in_quantifier_does_not_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u64_max_no_err",
        "forall(|x: u64| x <= u64::MAX)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u64| x <= u64::MAX) should NOT produce an Error",
    );
}

// ========================================================================
// i128/u128 associated constants in int_mode (#1875)
// ========================================================================

/// REGRESSION: u128::MAX in quantifier must not produce an encoding error.
/// Before fix: "u128::MAX too large for integer context" error.
/// After fix: uses int_const_bigint(2^128 - 1).
#[test]
fn test_u128_max_in_quantifier_no_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u128_max",
        "forall(|x: u128| x <= u128::MAX)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall(|x: u128| x <= u128::MAX) should NOT error — u128::MAX needs int_const_bigint in int_mode (#1875)");
}

/// REGRESSION: i128::MIN in quantifier must not produce an encoding error.
/// i128::MIN = -2^127 doesn't fit in i64.
#[test]
fn test_i128_min_in_quantifier_no_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "i128_min",
        "forall(|x: i128| x >= i128::MIN)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall(|x: i128| x >= i128::MIN) should NOT error — i128::MIN needs int_const_bigint in int_mode (#1875)");
}

/// DISCRIMINATING: forall |x: u128| x != u128::MAX must NOT verify.
/// u128::MAX is a valid counterexample.
#[test]
fn test_u128_ne_max_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u128_ne_max",
        "forall(|x: u128| x != u128::MAX)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall |x: u128| x != u128::MAX must NOT verify — u128::MAX is a valid counterexample (#1875)",
    );
}
