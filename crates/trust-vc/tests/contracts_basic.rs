// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic contract tests for trust_vc.
//!
//! Tests that requires!, ensures!, and old! macros compile and verify correctly.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::{ensures, old, requires};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_requires_compiles() {
    common::with_clean_verification(|| {
        // requires! should compile as a precondition check
        // Declare and bind variable for verification
        verify_macro::collect_variable("_x".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "_x == 5".to_string(),
            Some("contracts_basic.rs:25".to_string()),
        );
        let _x = 5;
        requires!(_x > 0);
        ensures!(_x > 0); // Add ensures to have something to verify

        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid precondition should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_compiles() {
    common::with_clean_verification(|| {
        // ensures! should compile as a postcondition check
        // Declare variable for verification
        trust_vc_core::verify_macro::collect_variable("result".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "result_value".to_string(),
            "result == 42".to_string(),
            Some("contracts_basic.rs:53".to_string()),
        );
        let result = 42;
        ensures!(result > 0);
        assert!(result > 0);

        // Verify the postcondition was collected
        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid postcondition should verify"
        );
    })
}

#[test]
fn test_requires_with_expression() {
    common::with_clean_verification(|| {
        // requires! with complex expression
        // Declare variables for verification (need underscore prefix to match usage)
        trust_vc_core::verify_macro::collect_variable("_a".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("_b".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_value".to_string(),
            "_a == 10".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_value".to_string(),
            "_b == 5".to_string(),
            None,
        );
        let _a = 10;
        let _b = 5;
        requires!(_a > _b);

        // Add an actual assertion to verify
        trust_vc::assert!(_a > _b);

        // Verify the assertion passes
        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Complex precondition should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_with_expression() {
    common::with_clean_verification(|| {
        // ensures! with complex expression
        // Declare variables for verification
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("y".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("z".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 3".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_value".to_string(),
            "y == 4".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "z_value".to_string(),
            "z == 7".to_string(),
            None,
        );
        let x = 3;
        let y = 4;
        let z = x + y;
        ensures!(z == x + y);
        assert_eq!(z, 7);

        // Verify the postcondition was collected
        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Complex postcondition should verify"
        );
    })
}

#[test]
fn test_old_compiles() {
    common::with_clean_verification(|| {
        // old! should compile and evaluate to the expression
        let x = 42;
        let result = old!(x);
        assert_eq!(result, 42);
    })
}

#[test]
fn test_old_with_arithmetic() {
    common::with_clean_verification(|| {
        // old! should work with expressions
        let x = 10;
        let old_plus_one = old!(x) + 1;
        assert_eq!(old_plus_one, 11);
    })
}

// test_old_in_closure removed: old!(values.len()) was unsound passthrough (#1836).
// Complex expressions in old!() now correctly produce a compile error.

#[test]
fn test_contracts_together() {
    common::with_clean_verification(|| {
        // Using requires! and ensures! in same function
        // Declare variables for verification
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("result".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "result_value".to_string(),
            "result == 10".to_string(),
            None,
        );
        let x = 5;
        requires!(x > 0);
        let result = x * 2;
        ensures!(result > x);
        assert_eq!(result, 10);

        // Verify both contracts were collected
        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Combined contracts should verify"
        );
    })
}

#[test]
fn test_invalid_requires_should_fail() {
    common::with_clean_verification(|| {
        // Test that invalid preconditions are rejected
        // Set up contradictory conditions that should fail
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );

        // This should fail because we assume x == 5 but require x > 10
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "invalid_requires".to_string(),
            "x > 10".to_string(),
            Some("contracts_basic.rs:234".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // We expect a counterexample since x=5 and 5 > 10 is false
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invalid precondition should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_ensures_should_fail() {
    common::with_clean_verification(|| {
        // Test that invalid postconditions are rejected
        // Set up conditions where postcondition cannot be met
        verify_macro::collect_variable("result".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "result_value".to_string(),
            "result == 42".to_string(),
            None,
        );

        // This should fail because result == 42 but we assert result < 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "invalid_ensures".to_string(),
            "result < 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // We expect a counterexample since result=42 and 42 < 0 is false
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invalid postcondition should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_old_with_ensures() {
    common::with_clean_verification(|| {
        // Typical pattern: old! inside ensures! context
        // Declare variables for verification
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("_old_x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "old_x_value".to_string(),
            "_old_x == 10".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 15".to_string(),
            None,
        );
        let mut x = 10;
        let _old_x = old!(x);
        x += 5;
        ensures!(x == _old_x + 5);
        assert_eq!(x, 15);

        // Verify the ensures with old value was collected
        // Use VerificationPipeline to actually verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "ensures! with old! should verify, but got: {:?}",
            result
        );
    })
}

#[test]
fn test_conflicting_requires_ensures_should_fail() {
    common::with_clean_verification(|| {
        // Test that conflicting requires and ensures are rejected
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 0 as precondition
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "requires_x_positive".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Assert x < 0 as postcondition - this conflicts!
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "ensures_x_negative".to_string(),
            "x < 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // We expect a counterexample since x cannot be both > 0 and < 0
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Conflicting requires/ensures should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_incorrect_old_value_should_fail() {
    common::with_clean_verification(|| {
        // Test that incorrect assumptions about old values are rejected
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("old_x".to_string(), "i32".to_string());

        // Set up old value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "old_x_value".to_string(),
            "old_x == 10".to_string(),
            None,
        );

        // Set up new value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 15".to_string(),
            None,
        );

        // This should fail - we assert wrong relationship between old and new
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "wrong_old_relationship".to_string(),
            "x == old_x + 10".to_string(), // Wrong: should be +5
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // We expect a counterexample since x=15, old_x=10, and 15 != 10+10
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Incorrect old value relationship should produce counterexample, got: {:?}",
            result
        );
    })
}
