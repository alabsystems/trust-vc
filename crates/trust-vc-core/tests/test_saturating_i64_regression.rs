//! Regression tests for #1685: i64/i128 saturating arithmetic panic
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Before the fix, `(1i64 << 63) - 1` in methods.rs panicked in debug mode
//! because `1i64 << 63` produces `i64::MIN`, and `i64::MIN - 1` overflows.
//! The fix replaces i64 arithmetic with BigInt for signed type bounds.

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

/// DISCRIMINATING: i64 saturating_add must not panic when computing type bounds.
///
/// Before fix: `(1i64 << 63) - 1` panics in debug mode.
/// After fix: BigInt arithmetic avoids i64 overflow entirely.
///
/// Declares x as i64 (width=64), which forces the saturating_add code path
/// through the signed bounds computation where the overflow lived.
#[test]
fn test_saturating_add_i64_no_panic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume(
        "x_is_max",
        "x == 9223372036854775807",
    )); // i64::MAX
        // i64::MAX.saturating_add(1) should equal i64::MAX (saturation)
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_max",
        "x.saturating_add(1) == 9223372036854775807",
    ));

    let result = ctx.verify();
    // The old code would panic before reaching this assertion.
    // With the #1685 fix, saturating_add encodes correctly and verifies.
    assert!(
        matches!(result, VerifyResult::Verified),
        "saturating_add on i64 must not produce an error (was panic before #1685 fix), got: {:?}",
        result
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
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume(
        "x_is_min",
        "x == -9223372036854775808",
    )); // i64::MIN
        // i64::MIN.saturating_sub(1) should equal i64::MIN (saturation)
    ctx.push_obligation(ProofObligation::assert(
        "sat_sub_min",
        "x.saturating_sub(1) == -9223372036854775808",
    ));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "saturating_sub on i64 must not produce an error (was panic before #1685 fix), got: {:?}",
        result
    );
}

/// Baseline: u32 saturating_add still works after BigInt refactor.
///
/// Guards against regression where the BigInt change might break
/// the existing u32 path (which worked before via i64 arithmetic).
#[test]
fn test_saturating_add_u32_baseline() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == 4294967295")); // u32::MAX
    ctx.push_obligation(ProofObligation::assert(
        "sat_add_u32",
        "x.saturating_add(1) == 4294967295",
    ));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "saturating_add on u32 must still work after BigInt refactor, got: {:?}",
        result
    );
}
