//! End-to-end integration tests for the full trust_vc pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests verify the complete flow from proc macros through
//! VC extraction to ay verification and result reporting.

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

/// Test the full pipeline: declare variables → add assumptions → assert → verify
#[test]
fn test_full_pipeline_simple_assertion() {
    common::with_clean_verification(|| {
        // Step 1: Declare variables (simulating what proc macros would do)
        collect_variable("x".to_string(), "i32".to_string());
        collect_variable("y".to_string(), "i32".to_string());

        // Step 2: Add an assumption
        collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 10".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Step 3: Add an assertion
        collect_obligation(
            ObligationKind::Assert,
            "sum_check".to_string(),
            "x + y == 15".to_string(),
            Some("test.rs:3:1".to_string()),
        );

        // Step 4: Run verification through the pipeline
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Step 5: Check the result
        assert!(
            matches!(result, VerifyResult::Verified),
            "Simple assertion x + y == 15 should verify, got: {:?}",
            result
        );
    })
}

/// Test counterexample generation through the full pipeline
#[test]
fn test_full_pipeline_counterexample() {
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("a".to_string(), "i32".to_string());

        // Add an assumption
        collect_obligation(
            ObligationKind::Assume,
            "a_positive".to_string(),
            "a > 0".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Add a false assertion
        collect_obligation(
            ObligationKind::Assert,
            "false_claim".to_string(),
            "a < 0".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Run verification
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should get a counterexample
        match result {
            VerifyResult::Counterexample {
                obligation_name,
                model,
                ..
            } => {
                assert!(
                    obligation_name.starts_with("false_claim"),
                    "Expected obligation starting with 'false_claim', got: {}",
                    obligation_name
                );
                assert!(
                    model.is_some(),
                    "Should have a model showing the counterexample"
                );
            }
            _ => panic!(
                "Expected counterexample for false assertion, got: {:?}",
                result
            ),
        }
    })
}

/// Test unsigned integer handling through the full pipeline
#[test]
fn test_full_pipeline_unsigned_integers() {
    common::with_clean_verification(|| {
        // Declare unsigned variables
        collect_variable("u".to_string(), "u32".to_string());
        collect_variable("v".to_string(), "u32".to_string());

        // Set values that would be negative if interpreted as signed
        collect_obligation(
            ObligationKind::Assume,
            "u_value".to_string(),
            "u == 4294967295".to_string(), // u32::MAX
            Some("test.rs:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "v_value".to_string(),
            "v == 1".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Assert unsigned comparison
        collect_obligation(
            ObligationKind::Assert,
            "unsigned_gt".to_string(),
            "u > v".to_string(), // u32::MAX > 1 should be true
            Some("test.rs:3:1".to_string()),
        );

        // Run verification
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX > 1 should verify with unsigned comparison, got: {:?}",
            result
        );
    })
}

/// Test requires obligations through the full pipeline.
///
/// Requires is a precondition (assumption) in function body verification
/// (fixes #755, #1078). It constrains the verification context so that
/// subsequent assertions can rely on the precondition holding.
#[test]
fn test_full_pipeline_requires_as_assumption() {
    common::with_clean_verification(|| {
        // Declare the variable first
        collect_variable("x".to_string(), "i32".to_string());

        // Add a requires obligation (precondition) - this is an assumption
        collect_obligation(
            ObligationKind::Requires,
            "positive_input".to_string(),
            "x > 0".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Assert something that follows from the precondition
        collect_obligation(
            ObligationKind::Assert,
            "positive_check".to_string(),
            "x > 0".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // With requires(x > 0) as assumption, assert(x > 0) should verify
        assert!(
            matches!(result, VerifyResult::Verified),
            "Requires should act as assumption enabling assertion, got: {:?}",
            result
        );
    })
}

/// Test that requires alone (no assertions) returns Error (#1859).
///
/// Assumptions-only contexts are rejected because they have nothing to prove.
#[test]
fn test_full_pipeline_requires_only_returns_error() {
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        // Only a requires, no assertions
        collect_obligation(
            ObligationKind::Requires,
            "positive_input".to_string(),
            "x > 0".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Requires alone is assumptions-only, which is an error (#1859).
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Requires-only context should return Error (#1859), got: {:?}",
            result
        );
    })
}

/// Test the alternate verify_collected API
#[test]
fn test_full_pipeline_verify_collected_api() {
    common::with_clean_verification(|| {
        // Use the verify_collected API instead of VerificationPipeline
        collect_variable("n".to_string(), "i32".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 42".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assert,
            "n_check".to_string(),
            "n == 42".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Use verify_collected instead
        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "verify_collected should work for simple assertions, got: {:?}",
            result
        );
    })
}

/// Test termination checking through the full pipeline
#[test]
fn test_full_pipeline_termination_checking() {
    common::with_clean_verification(|| {
        // Simulate a decreases clause check
        collect_variable("n".to_string(), "u64".to_string());
        collect_variable("n_prev".to_string(), "u64".to_string());

        // Current value
        collect_obligation(
            ObligationKind::Assume,
            "n_current".to_string(),
            "n == 5".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Previous value
        collect_obligation(
            ObligationKind::Assume,
            "n_previous".to_string(),
            "n_prev == 10".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Check measure decreases
        collect_obligation(
            ObligationKind::MeasureDecreases,
            "termination".to_string(),
            "n < n_prev".to_string(),
            Some("test.rs:3:1".to_string()),
        );

        // Check measure is non-negative
        collect_obligation(
            ObligationKind::MeasureNonNegative,
            "non_negative".to_string(),
            "n >= 0".to_string(),
            Some("test.rs:4:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Termination check should verify, got: {:?}",
            result
        );
    })
}

/// Test complex expression parsing through the full pipeline
#[test]
fn test_full_pipeline_complex_expressions() {
    common::with_clean_verification(|| {
        // Declare multiple variables
        collect_variable("a".to_string(), "i32".to_string());
        collect_variable("b".to_string(), "i32".to_string());
        collect_variable("c".to_string(), "i32".to_string());

        // Set up values
        collect_obligation(
            ObligationKind::Assume,
            "a_val".to_string(),
            "a == 10".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "b_val".to_string(),
            "b == 20".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "c_val".to_string(),
            "c == 5".to_string(),
            Some("test.rs:3:1".to_string()),
        );

        // Complex assertion with multiple operations
        collect_obligation(
            ObligationKind::Assert,
            "complex".to_string(),
            "(a + b) * c == 150 && a < b && b - a == 10".to_string(),
            Some("test.rs:4:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Complex expression should verify, got: {:?}",
            result
        );
    })
}

/// Test that empty pipeline returns appropriate error
#[test]
fn test_full_pipeline_empty_context_error() {
    common::with_clean_verification(|| {
        // Don't add any obligations
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        match result {
            VerifyResult::Error { message } => {
                assert!(
                    message.contains("empty") || message.contains("no obligations"),
                    "Empty context should produce meaningful error, got: {}",
                    message
                );
            }
            _ => panic!("Empty context should return Error, got: {:?}", result),
        }
    })
}

/// Test ensures obligations through the full pipeline
#[test]
fn test_full_pipeline_ensures_verification() {
    common::with_clean_verification(|| {
        // Declare variables for postcondition checking
        collect_variable("result".to_string(), "i32".to_string());
        collect_variable("x".to_string(), "i32".to_string());

        // Assume x is 5
        collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Assume result is x * 2
        collect_obligation(
            ObligationKind::Assume,
            "computation".to_string(),
            "result == x * 2".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Ensure result is 10 (postcondition)
        collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "result == 10".to_string(),
            Some("test.rs:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Ensures postcondition should verify, got: {:?}",
            result
        );
    })
}

/// Test ensures obligations that should fail
#[test]
fn test_full_pipeline_ensures_failure() {
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("result".to_string(), "i32".to_string());
        collect_variable("x".to_string(), "i32".to_string());

        // Assume x is 5
        collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Assume result is x * 2 (which is 10)
        collect_obligation(
            ObligationKind::Assume,
            "computation".to_string(),
            "result == x * 2".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        // Ensure result is 20 (wrong postcondition - should fail)
        collect_obligation(
            ObligationKind::Ensures,
            "wrong_postcondition".to_string(),
            "result == 20".to_string(),
            Some("test.rs:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should get counterexample since result is 10, not 20
        match result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.starts_with("wrong_postcondition"),
                    "Wrong ensures should produce counterexample, got: {}",
                    obligation_name
                );
            }
            _ => panic!("Wrong ensures should fail, got: {:?}", result),
        }
    })
}

/// Test division by zero detection
#[test]
fn test_full_pipeline_division_by_zero() {
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("a".to_string(), "i32".to_string());
        collect_variable("b".to_string(), "i32".to_string());
        collect_variable("result".to_string(), "i32".to_string());

        // Set b to zero
        collect_obligation(
            ObligationKind::Assume,
            "b_zero".to_string(),
            "b == 0".to_string(),
            Some("test.rs:1:1".to_string()),
        );

        // Try to divide by b (should be able to verify this is problematic)
        collect_obligation(
            ObligationKind::Assert,
            "no_div_zero".to_string(),
            "b != 0".to_string(),
            Some("test.rs:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should get counterexample since b == 0 contradicts b != 0
        match result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.starts_with("no_div_zero"),
                    "Division by zero check should fail, got: {}",
                    obligation_name
                );
            }
            _ => panic!(
                "Division by zero check should produce counterexample, got: {:?}",
                result
            ),
        }
    })
}
