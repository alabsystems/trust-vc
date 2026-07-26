// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comprehensive test demonstrating the correct semantics of requires!
//!
//! This test shows that there are TWO different verification contexts:
//! 1. Function body verification (requires = assumption)
//! 2. Call site verification (requires = assertion to check)
//!
//! Currently we only do function body verification, so requires MUST be an assumption.

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_function_body_verification_semantics() {
    common::with_clean_verification(|| {
        // When verifying a function body in isolation, requires creates assumptions

        // Function: f(x: i32) with requires!(x > 0) and ensures!(x > -10)
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x > 0".to_string(),
            Some("test:1:1".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > -10".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // This should verify because:
        // - We ASSUME x > 0 (from requires)
        // - Given x > 0, we can PROVE x > -10 (the ensures)
        assert!(
            matches!(result, VerifyResult::Verified),
            "Function body verification should treat requires as assumption. Got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_false_means_unreachable() {
    common::with_clean_verification(|| {
        // requires(false) means "this function can never be called"
        // It's not a bug - it's a specification that the function is unreachable

        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "unreachable".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        // With requires(false), ANY postcondition is vacuously true
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "anything".to_string(),
            "1 == 2".to_string(), // Obviously false, but vacuously true
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #2258: contradictory assumptions (requires(false)) detected as vacuous truth
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("vacuously true")),
            "requires(false) + ensures(1==2) should be detected as vacuously true, got: {:?}",
            result
        );
    })
}

#[test]
fn test_call_site_verification_would_be_different() {
    common::with_clean_verification(|| {
        // This test documents what WOULD happen if we were verifying call sites
        // At a call site, we would CHECK that the precondition holds

        // Simulate: calling f(x) where f has requires!(x > 0)
        // and we're calling with x = -5
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // At call site, we would assert the precondition
        verify_macro::collect_obligation(
            ObligationKind::Assert, // Note: Assert, not Requires!
            "call_site_check".to_string(),
            "x > 0".to_string(),
            Some("call:1:1".to_string()),
        );

        // Assume x = -5 at the call site
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == -5".to_string(),
            Some("call:0:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // This should fail because x = -5 doesn't satisfy x > 0
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Call site verification would check precondition as assertion. Got: {:?}",
            result
        );
    })
}

#[test]
fn test_implication_verification() {
    common::with_clean_verification(|| {
        // Test logical implication: requires P, ensures Q means P => Q

        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // requires: x >= 10
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x >= 10".to_string(),
            Some("test:1:1".to_string()),
        );

        // ensures: x > 5
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > 5".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should verify because x >= 10 implies x > 5
        assert!(
            matches!(result, VerifyResult::Verified),
            "x >= 10 should imply x > 5. Got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_implication() {
    common::with_clean_verification(|| {
        // Test invalid implication: requires P, ensures Q where P doesn't imply Q

        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // requires: x > 0
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x > 0".to_string(),
            Some("test:1:1".to_string()),
        );

        // ensures: x > 100 (not implied by x > 0)
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > 100".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should fail because x > 0 doesn't imply x > 100
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "x > 0 doesn't imply x > 100, should get counterexample. Got: {:?}",
            result
        );
    })
}
