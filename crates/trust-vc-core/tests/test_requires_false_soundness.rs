//! Test for critical soundness bug with requires(false)
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable};
use trust_vc_core::VerifyResult;

/// requires(false) alone returns Error — nothing to prove (#1859).
/// Previously vacuously Verified, but assumptions-only is now an error.
#[test]
fn test_requires_false_returns_error() {
    common::with_clean_verification(|| {
        // In callee-side verification, requires(false) is an assumption.
        // With only assumptions and no assertions, the result is Error (#1859).
        collect_obligation(
            ObligationKind::Requires,
            "impossible".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(false) alone should return Error (#1859), got: {:?}",
            result
        );
    })
}

/// requires(1 == 0) alone returns Error — nothing to prove (#1859).
#[test]
fn test_requires_one_equals_zero_returns_error() {
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Requires,
            "contradiction".to_string(),
            "1 == 0".to_string(),
            Some("test:1:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(1 == 0) alone should return Error (#1859), got: {:?}",
            result
        );
    })
}

/// requires(true) alone returns Error — nothing to prove (#1859).
#[test]
fn test_requires_true_alone_returns_error() {
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Requires,
            "tautology".to_string(),
            "true".to_string(),
            Some("test:1:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(true) alone should return Error (#1859), got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_with_satisfying_assumption() {
    common::with_clean_verification(|| {
        // Test that assume + requires interact correctly with a non-trivial assertion.
        // Assume x > 5, requires x > 0 (weaker precondition), then assert x > 3.
        // The assertion requires the solver to derive x > 5 ⟹ x > 3.
        // (#1595: was assume(x>0) + requires(x>0) with no assertion — vacuously verified)
        collect_variable("x".to_string(), "i32".to_string());

        // Stronger assumption
        collect_obligation(
            ObligationKind::Assume,
            "x_large".to_string(),
            "x > 5".to_string(),
            Some("test:1:1".to_string()),
        );

        // Weaker requires (also an assumption in callee-side verification)
        collect_obligation(
            ObligationKind::Requires,
            "requires_positive".to_string(),
            "x > 0".to_string(),
            Some("test:2:1".to_string()),
        );

        // Non-trivial assertion: x > 5 implies x > 3
        collect_obligation(
            ObligationKind::Assert,
            "derived_bound".to_string(),
            "x > 3".to_string(),
            Some("test:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 5 with requires(x > 0) should imply x > 3, got: {:?}",
            result
        );
    })
}

/// Contradicting assumptions with no assertions returns Error (#1859).
#[test]
fn test_requires_contradicting_assumption_returns_error() {
    common::with_clean_verification(|| {
        collect_variable("y".to_string(), "i32".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "y_negative".to_string(),
            "y < 0".to_string(),
            Some("test:1:1".to_string()),
        );

        // In callee-side verification, Requires is also an assumption.
        // So we have: assume(y < 0) AND assume(y > 0) = unsatisfiable assumptions.
        // With no assertions, result is Error (#1859).
        collect_obligation(
            ObligationKind::Requires,
            "requires_positive".to_string(),
            "y > 0".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Contradicting assumptions with no assertions should return Error (#1859), got: {:?}",
            result
        );
    })
}
