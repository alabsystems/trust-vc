//! Integration tests for Ensures obligation kind through ay.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Ensures (postcondition) obligations are treated as assertions by the
//! encoder (alongside Assert, MeasureNonNegative, MeasureDecreases).
//! These tests verify that Ensures obligations are properly checked by ay,
//! not silently dropped or treated as assumptions.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests invoke ay verification through `VerificationContext::verify()`.

use trust_vc_core::vc::{ObligationKind, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

mod common;

fn obligation(
    name: &str,
    condition: &str,
    kind: ObligationKind,
    location: &str,
) -> ProofObligation {
    ProofObligation::new(name, condition, kind).with_location(location)
}

/// Ensures(true) should verify — trivially valid postcondition.
#[test]
fn test_ensures_true_verifies() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(obligation(
            "postcondition",
            "true",
            ObligationKind::Ensures,
            "test.rs:1:1",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "ensures(true) must verify, got: {:?}",
            result
        );
    })
}

/// Ensures(false) should produce a counterexample — unsatisfiable postcondition.
#[test]
fn test_ensures_false_produces_counterexample() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(obligation(
            "impossible_post",
            "false",
            ObligationKind::Ensures,
            "test.rs:1:1",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures(false) must produce Counterexample, got: {:?}",
            result
        );
    })
}

/// Ensures with a variable: requires(x > 0) (assumption) + ensures(x > 0) should verify.
#[test]
fn test_ensures_with_requires_assumption() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Requires acts as assumption in function body verification
        ctx.push_obligation(obligation(
            "precondition",
            "x > 0",
            ObligationKind::Requires,
            "test.rs:1:1",
        ));

        // Ensures is the postcondition to check
        ctx.push_obligation(obligation(
            "postcondition",
            "x > 0",
            ObligationKind::Ensures,
            "test.rs:2:1",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "requires(x > 0) + ensures(x > 0) must verify, got: {:?}",
            result
        );
    })
}

/// Ensures without assumptions: ensures(x > 0) should fail for unconstrained x.
#[test]
fn test_ensures_without_assumptions_fails() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(obligation(
            "unconstrained_post",
            "x > 0",
            ObligationKind::Ensures,
            "test.rs:1:1",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures(x > 0) without assumptions must fail (x could be <= 0), got: {:?}",
            result
        );
    })
}

/// Mixed Assert + Ensures: both should be checked.
/// If one fails, that specific obligation name should appear in the counterexample.
#[test]
fn test_mixed_assert_and_ensures() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(ProofObligation::assume("x_bound", "x == 5"));

        // Assert that should pass
        ctx.push_obligation(ProofObligation::assert("assert_check", "x == 5"));

        // Ensures that should also pass
        ctx.push_obligation(obligation(
            "ensures_check",
            "x > 0",
            ObligationKind::Ensures,
            "test.rs:3:1",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Both assert(x == 5) and ensures(x > 0) should verify, got: {:?}",
            result
        );
    })
}

/// Ensures with wrong postcondition: requires(x > 0) + ensures(x < 0) should fail.
#[test]
fn test_ensures_contradicts_precondition() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(obligation(
            "precondition",
            "x > 0",
            ObligationKind::Requires,
            "test.rs:1:1",
        ));

        ctx.push_obligation(obligation(
            "bad_postcondition",
            "x < 0",
            ObligationKind::Ensures,
            "test.rs:2:1",
        ));

        let result = ctx.verify();
        match result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.starts_with("bad_postcondition"),
                    "Failed obligation should be the bad postcondition, got: {}",
                    obligation_name
                );
            }
            _ => panic!(
                "ensures(x < 0) with requires(x > 0) must produce Counterexample, got: {:?}",
                result
            ),
        }
    })
}
