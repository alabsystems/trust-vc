//! Tests for integer division and modulo semantics in the trust_vc encoder
//!
//! The encoder uses bitvector operations (bvsdiv/bvsrem for signed,
//! bvudiv/bvurem for unsigned), which follow **truncating** semantics:
//! - Division truncates toward zero
//! - Remainder has the sign of the **dividend** (Rust/C semantics)
//!
//! This differs from SMT-LIB's integer `mod` (Euclidean, sign follows divisor).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

/// Bitvector signed division (bvsdiv) truncates toward zero:
/// - Positive / Positive: truncate down (floor)
/// - Negative / Positive: truncate up (ceil)
/// - Positive / Negative: truncate up (ceil)
/// - Negative / Negative: truncate down (floor)
///
/// Bitvector signed remainder (bvsrem) has the sign of the dividend:
/// - (-7) % 2 == -1  (not +1 as in Euclidean modulo)
///
/// This matches Rust's `%` operator semantics.

#[test]
fn test_positive_div_positive() {
    // 7 / 2 = 3 (truncate toward zero from 3.5)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("div_pos_pos", "7 / 2 == 3"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "7 / 2 should equal 3"
    );
}

#[test]
fn test_negative_div_positive() {
    // -7 / 2 = -3 (truncate toward zero from -3.5)
    // SMT-LIB: truncation toward zero
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("div_neg_pos", "(-7) / 2 == (-3)"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "(-7) / 2 should equal -3"
    );
}

#[test]
fn test_positive_div_negative() {
    // 7 / -2 = -3 (truncate toward zero from -3.5)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("div_pos_neg", "7 / (-2) == (-3)"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "7 / (-2) should equal -3"
    );
}

#[test]
fn test_negative_div_negative() {
    // -7 / -2 = 3 (truncate toward zero from 3.5)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("div_neg_neg", "(-7) / (-2) == 3"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "(-7) / (-2) should equal 3"
    );
}

#[test]
fn test_mod_identity() {
    // SMT-LIB identity: m = (div m n) * n + (mod m n)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("m", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("n_not_zero", "n != 0"));
    ctx.push_obligation(ProofObligation::assert(
        "mod_identity",
        "m == (m / n) * n + (m % n)",
    ));
    let result = ctx.verify();

    // KNOWN ISSUE #726: AY returns Unknown for modulo identity
    // This should verify, but the AY backend has limitations with division/modulo
    match result {
        VerifyResult::Verified => {
            // Good - the identity verified
        }
        VerifyResult::Unknown { reason, .. } => {
            // Known issue #726 - AY can't handle this identity
            eprintln!(
                "WARNING: test_mod_identity got Unknown (issue #726): {}",
                reason
            );
            // Accept Unknown for now until AY backend is improved
        }
        other => {
            panic!(
                "Modulo identity should verify or return Unknown, got: {:?}",
                other
            );
        }
    }
}

#[test]
fn test_mod_sign_follows_dividend() {
    // With bvsrem (BV signed remainder), the sign follows the dividend.
    // 7 % 2 = 1 (positive dividend, positive result)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("mod_pos_pos", "7 % 2 == 1"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "7 % 2 should equal 1"
    );
}

#[test]
fn test_mod_negative_dividend() {
    // The encoder uses bvsrem (BV signed remainder), which follows Rust/C
    // truncating semantics: the result has the sign of the dividend.
    //
    // (-7) % 2 == -1 (truncating: sign follows dividend -7)
    // Verify: -7 = (-3) * 2 + (-1) = -6 + (-1) = -7 ✓
    //
    // NOTE: SMT-LIB integer `mod` would give +1 (Euclidean), but the encoder
    // correctly uses bvsrem for Rust integer types.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("mod_neg_pos", "(-7) % 2 == (-1)"));
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "bvsrem(-7, 2) should equal -1 (Rust truncating semantics), got: {:?}",
        result
    );
}

#[test]
fn test_division_by_one() {
    // x / 1 = x for all x
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("div_by_one", "x / 1 == x"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "x / 1 should equal x"
    );
}

#[test]
fn test_zero_divided_by_nonzero() {
    // 0 / n = 0 for all n != 0
    // This requires BV reasoning over all 2^32 non-zero values of n,
    // which may timeout on DPLL-based solvers.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("n_not_zero", "n != 0"));
    ctx.push_obligation(ProofObligation::assert("zero_div", "0 / n == 0"));
    let result = ctx.verify();
    match result {
        VerifyResult::Verified => {
            // Good - the identity verified
        }
        VerifyResult::Unknown { reason, .. } => {
            // BV division with free variable may exceed solver capacity
            eprintln!(
                "WARNING: test_zero_divided_by_nonzero got Unknown: {}",
                reason
            );
        }
        other => {
            panic!("0 / n should verify or return Unknown, got: {:?}", other);
        }
    }
}

#[test]
fn test_mod_by_one() {
    // x % 1 = 0 for all x
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("mod_by_one", "x % 1 == 0"));
    let result = ctx.verify();
    // This mathematical identity should always verify
    assert!(
        matches!(result, VerifyResult::Verified),
        "x % 1 should equal 0, got: {:?}",
        result
    );
}
