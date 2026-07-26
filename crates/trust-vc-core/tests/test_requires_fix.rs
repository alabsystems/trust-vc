//! Tests for the requires! macro semantics fix
//!
//! This file tests the soundness fix #1439 where requires! was incorrectly
//! treated as an assumption rather than an assertion. After the fix, requires!
//! conditions are properly verified to ensure they can be satisfied.
//!
//! Copyright 2026 Andrew Yates
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::{ObligationKind, VerificationContext};
use trust_vc_core::VerifyResult;

fn obligation(
    name: &str,
    condition: &str,
    kind: ObligationKind,
    location: &str,
) -> trust_vc_core::vc::ProofObligation {
    trust_vc_core::vc::ProofObligation::new(name, condition, kind).with_location(location)
}

#[test]
fn test_requires_is_verified() {
    // Test that requires is properly verified as an assertion in CallSite mode (#1692)
    let mut ctx = VerificationContext::new().with_call_site_mode();

    // Declare variable x
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add requires that should fail: x > 0 (with no assumptions about x)
    ctx.push_obligation(obligation(
        "requires_x_positive",
        "x > 0",
        ObligationKind::Requires,
        "test:1:1",
    ));

    let result = ctx.verify();

    match result {
        VerifyResult::Counterexample { .. } => {
            // Good: requires is properly verified and can fail (x could be <= 0)
        }
        _ => panic!(
            "requires! should be verified as assertion. Got: {:?}",
            result
        ),
    }
}

#[test]
fn test_requires_with_valid_precondition() {
    // Test that valid requires can be verified when assumptions support it (CallSite mode)
    let mut ctx = VerificationContext::new().with_call_site_mode();

    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Assume x is 10
    ctx.push_obligation(obligation(
        "x_value",
        "x == 10",
        ObligationKind::Assume,
        "test:1:1",
    ));

    // Requires x > 0 should now verify since x = 10
    ctx.push_obligation(obligation(
        "requires_positive",
        "x > 0",
        ObligationKind::Requires,
        "test:2:1",
    ));

    let result = ctx.verify();

    match result {
        VerifyResult::Verified => {
            // Good: requires is satisfied by the assumption
        }
        _ => panic!("Valid requires should verify. Got: {:?}", result),
    }
}

#[test]
fn test_ensures_is_checked() {
    // Ensure that ensures! is properly checked as an assertion
    let mut ctx = VerificationContext::new();

    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Assume x = 42
    ctx.push_obligation(obligation(
        "x_value",
        "x == 42",
        ObligationKind::Assume,
        "test:1:1",
    ));

    // Add ensures that should fail: x < 0 (but x = 42)
    ctx.push_obligation(obligation(
        "ensures_negative",
        "x < 0",
        ObligationKind::Ensures,
        "test:2:1",
    ));

    let result = ctx.verify();

    match result {
        VerifyResult::Counterexample { .. } => {
            // Good: ensures is properly checked and fails
        }
        _ => panic!(
            "ensures! with false condition should not verify. Got: {:?}",
            result
        ),
    }
}
