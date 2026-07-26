// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for ensures! macro - verify that invalid postconditions fail
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid ensures clauses

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_ensures_false_fails() {
    common::with_clean_verification(|| {
        // Test that ensures!(false) produces a counterexample
        // Add ensures!(false) - this should FAIL verification
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_false".to_string(),
            "false".to_string(),
            Some("test_ensures_negative:false".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures!(false) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_impossible_condition_fails() {
    common::with_clean_verification(|| {
        // Test that impossible ensures conditions are rejected
        // Add ensures!(1 > 2) - this should FAIL verification
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_impossible".to_string(),
            "1 > 2".to_string(),
            Some("test_ensures_negative:impossible".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures!(1 > 2) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_contradictory_conditions_fail() {
    common::with_clean_verification(|| {
        // Test that contradictory ensures conditions fail
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Add contradictory ensures conditions
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_x_large".to_string(),
            "x > 100".to_string(),
            Some("test_ensures_negative:contradiction1".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_x_small".to_string(),
            "x < 50".to_string(),
            Some("test_ensures_negative:contradiction2".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Contradictory ensures conditions should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_not_established_fails() {
    common::with_clean_verification(|| {
        // Test that ensures conditions that aren't established fail
        // Declare variable
        verify_macro::collect_variable("result".to_string(), "i32".to_string());

        // Assume input value
        verify_macro::collect_variable("input".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "input_value".to_string(),
            "input == 5".to_string(),
            Some("test_ensures_negative:input".to_string()),
        );

        // Simulate function body: result = input + 1
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "computation".to_string(),
            "result == input + 1".to_string(),
            Some("test_ensures_negative:body".to_string()),
        );

        // Ensures that is NOT satisfied: result > 10
        // Since input = 5 and result = 6, this should fail
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_result_large".to_string(),
            "result > 10".to_string(),
            Some("test_ensures_negative:not_established".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Ensures condition not established should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_arithmetic_overflow_fails() {
    common::with_clean_verification(|| {
        // Test that ensures with potential overflow fails
        // Declare variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Set up values near overflow
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 2147483647".to_string(), // i32::MAX
            Some("test_ensures_negative:overflow_x".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 1".to_string(),
            Some("test_ensures_negative:overflow_y".to_string()),
        );

        // Ensures that would cause overflow
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_sum".to_string(),
            "x + y > x".to_string(), // This would overflow in i32
            Some("test_ensures_negative:overflow".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // The verifier should either reject this or return Unknown due to overflow
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Ensures with overflow should not verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_and_assert_both_checked() {
    common::with_clean_verification(|| {
        // Test that Ensures and Assert behave the same for verification
        // Both are checked, not assumed
        // Test with Ensures
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "ensures_false".to_string(),
            "5 > 10".to_string(), // False postcondition
            Some("test_ensures_negative:ensures".to_string()),
        );

        let pipeline1 = VerificationPipeline::collect_from_macros();
        let result1 = pipeline1.verify();

        assert!(
            matches!(result1, VerifyResult::Counterexample { .. }),
            "Ensures false should fail, got: {:?}",
            result1
        );

        // Test with Assert
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_false".to_string(),
            "5 > 10".to_string(), // False assertion
            Some("test_ensures_negative:assert".to_string()),
        );

        let pipeline2 = VerificationPipeline::collect_from_macros();
        let result2 = pipeline2.verify();

        assert!(
            matches!(result2, VerifyResult::Counterexample { .. }),
            "Assert false should also fail, got: {:?}",
            result2
        );
    })
}
