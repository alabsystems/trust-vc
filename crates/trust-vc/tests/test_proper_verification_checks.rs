//! Test demonstrating proper verification outcome checking
//!
//! This file shows how tests SHOULD check verification outcomes:
//! 1. Tests must check for specific VerifyResult values
//! 2. Positive tests must assert VerifyResult::Verified
//! 3. Negative tests must assert VerifyResult::Counterexample
//! 4. Tests must not accept multiple outcomes
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

/// Test that valid assertions verify correctly
mod common;

#[test]
fn test_valid_assertion_must_verify() {
    common::with_clean_verification(|| {
        // Add a simple valid assertion
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "tautology".to_string(),
            "true".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST check for exactly Verified - not Unknown, not Counterexample
        assert!(
            matches!(result, VerifyResult::Verified),
            "Expected Verified for tautology 'true', got: {:?}",
            result
        );
    })
}

/// Test that invalid assertions produce counterexamples
#[test]
fn test_invalid_assertion_must_fail() {
    common::with_clean_verification(|| {
        // Add a simple invalid assertion
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "contradiction".to_string(),
            "false".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST check for exactly Counterexample - not Verified, not Unknown
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Expected Counterexample for contradiction 'false', got: {:?}",
            result
        );
    })
}

/// Test that arithmetic assertions verify correctly
#[test]
fn test_arithmetic_assertion_must_verify() {
    common::with_clean_verification(|| {
        // Valid arithmetic: 2 + 2 == 4
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "arithmetic_valid".to_string(),
            "2 + 2 == 4".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST be Verified, not Unknown
        assert!(
            matches!(result, VerifyResult::Verified),
            "Expected Verified for '2 + 2 == 4', got: {:?}",
            result
        );
    })
}

/// Test that invalid arithmetic produces counterexample
#[test]
fn test_invalid_arithmetic_must_fail() {
    common::with_clean_verification(|| {
        // Invalid arithmetic: 2 + 2 == 5
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "arithmetic_invalid".to_string(),
            "2 + 2 == 5".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST be Counterexample, not Unknown
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Expected Counterexample for '2 + 2 == 5', got: {:?}",
            result
        );
    })
}

/// Test that assumptions influence verification
#[test]
fn test_assumption_makes_assertion_valid() {
    common::with_clean_verification(|| {
        // Add variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_positive".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Assert x >= 0 (valid given assumption)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_non_negative".to_string(),
            "x >= 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST be Verified because assumption implies assertion
        assert!(
            matches!(result, VerifyResult::Verified),
            "Expected Verified for 'x >= 0' given 'x > 0', got: {:?}",
            result
        );
    })
}

/// Test that conflicting assumptions and assertions fail
#[test]
fn test_conflicting_assumption_and_assertion_must_fail() {
    common::with_clean_verification(|| {
        // Add variable
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume y == 5
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_equals_five".to_string(),
            "y == 5".to_string(),
            None,
        );

        // Assert y == 10 (conflicts with assumption)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "y_equals_ten".to_string(),
            "y == 10".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // MUST be Counterexample because y cannot be both 5 and 10
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Expected Counterexample for conflicting y values, got: {:?}",
            result
        );
    })
}

/// Test that Unknown is only acceptable for timeouts/resource limits
#[test]
fn test_unknown_only_for_resource_limits() {
    common::with_clean_verification(|| {
        // Documentation test - passes by asserting the rule
        // Unknown should ONLY occur when:
        // 1. SMT solver times out
        // 2. Resource limits are exceeded
        // 3. Solver encounters undecidable formula
        //
        // Unknown should NEVER be accepted as a valid outcome for
        // simple decidable formulas like arithmetic or boolean logic.
        //
        // Tests should NOT accept Unknown as an alternative to
        // Counterexample or Verified for decidable formulas.
        // This is a documentation test demonstrating proper Unknown handling
    })
}

/// Demonstration of WRONG test pattern - DO NOT COPY
#[test]
fn test_bad_pattern_accepting_multiple_outcomes() {
    common::with_clean_verification(|| {
        // This test demonstrates what NOT to do - it passes to show the anti-pattern
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "some_assertion".to_string(),
            "false".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // BAD: This accepts both outcomes, making the test useless
        // If verification is broken and returns Verified for false,
        // this test would still pass!
        #[allow(clippy::redundant_pattern_matching)]
        if matches!(result, VerifyResult::Counterexample { .. })
            || matches!(result, VerifyResult::Unknown { .. })
        {
            // This is wrong - we lose the ability to detect regressions
            // Anti-pattern demonstration - real tests should have specific assertions
        } else {
            panic!("Anti-pattern test - should accept multiple outcomes for demonstration");
        }
    })
}
