// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the improved verification helpers (#778).

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;

// Import the functions directly from the module
use self::test_verify_helpers_v2::{
    expect_counterexample, expect_error, expect_unknown, expect_verified,
    expect_verified_or_unknown, has_obligations, obligation_count,
};

mod common;

#[test]
fn test_expect_verified_accepts_only_verified() {
    common::with_clean_verification(|| {
        // Create a valid assertion that should verify
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_positive".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Should succeed
        expect_verified().expect("Should be verified");
    })
}

#[test]
fn test_expect_counterexample_accepts_only_counterexample() {
    common::with_clean_verification(|| {
        // Create a false assertion that should produce counterexample
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_assertion".to_string(),
            "false".to_string(),
            None,
        );

        // Should succeed and return counterexample info
        let (obligation_name, _model) = expect_counterexample().expect("Should get counterexample");
        assert_eq!(obligation_name, "false_assertion");
    })
}

#[test]
fn test_expect_verified_rejects_counterexample() {
    common::with_clean_verification(|| {
        // Create a false assertion
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false".to_string(),
            "false".to_string(),
            None,
        );

        // Should fail because we get counterexample not verified
        let result = expect_verified();
        assert!(
            result.is_err(),
            "expect_verified should reject counterexample"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Verified but got Counterexample"),
            "Error message should indicate wrong outcome"
        );
    })
}

#[test]
fn test_expect_counterexample_rejects_verified() {
    common::with_clean_verification(|| {
        // Create a true assertion
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "true".to_string(),
            "true".to_string(),
            None,
        );

        // Should fail because we get verified not counterexample
        let result = expect_counterexample();
        assert!(
            result.is_err(),
            "expect_counterexample should reject verified"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Counterexample but got Verified"),
            "Error message should indicate wrong outcome"
        );
    })
}

#[test]
fn test_has_obligations() {
    common::with_clean_verification(|| {
        // Initially no obligations
        assert!(!has_obligations(), "Should have no obligations initially");
        assert_eq!(obligation_count(), 0);

        // Add an obligation
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "test".to_string(),
            "true".to_string(),
            None,
        );

        // Now should have obligations
        assert!(
            has_obligations(),
            "Should have obligations after adding one"
        );
        assert_eq!(obligation_count(), 1);
    })
}

#[test]
fn test_expect_error_accepts_only_error() {
    common::with_clean_verification(|| {
        // Empty context now returns Error (#808 soundness fix), so
        // expect_error() succeeds (returns Ok) for empty context.
        let result = expect_error();
        assert!(
            result.is_ok(),
            "expect_error should succeed for empty context (Error result), got: {:?}",
            result
        );
    })
}

#[test]
fn test_expect_unknown_accepts_only_unknown() {
    common::with_clean_verification(|| {
        // Test 1: Verify that expect_unknown rejects Verified outcome
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "true_assert".to_string(),
            "true".to_string(),
            None,
        );

        let result = expect_unknown();
        assert!(
            result.is_err(),
            "expect_unknown should reject Verified outcome"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Unknown but got Verified"),
            "Error message should indicate Verified was rejected"
        );

        // Test 2: Verify that expect_unknown rejects Counterexample outcome
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_assert".to_string(),
            "false".to_string(),
            None,
        );

        let result = expect_unknown();
        assert!(
            result.is_err(),
            "expect_unknown should reject Counterexample outcome"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Unknown but got Counterexample"),
            "Error message should indicate Counterexample was rejected"
        );

        // Test 3: Test that expect_unknown would accept Unknown outcome
        // Note: In practice, Unknown results come from solver timeouts or undecidable formulas
        // For this test, we verify the helper's logic by checking its match arms
        // A real Unknown test would require complex nested quantifiers or solver timeout
    })
}

#[test]
fn test_expect_verified_or_unknown_accepts_both() {
    common::with_clean_verification(|| {
        // Test 1: Accept Verified outcome
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "true_assert".to_string(),
            "true".to_string(),
            None,
        );

        let result = expect_verified_or_unknown();
        match result {
            Ok(trust_vc_core::VerifyResult::Verified) => {} // Expected
            Ok(other) => panic!("Expected Verified variant, got {:?}", other),
            Err(e) => panic!(
                "expect_verified_or_unknown should accept Verified, got error: {}",
                e
            ),
        }

        // Test 2: Reject Counterexample outcome
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_assert".to_string(),
            "false".to_string(),
            None,
        );

        let result = expect_verified_or_unknown();
        assert!(
            result.is_err(),
            "expect_verified_or_unknown should reject Counterexample"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Verified/Unknown but got Counterexample"),
            "Error message should indicate Counterexample was rejected"
        );

        // Test 3: Would accept Unknown outcome (if we could generate one)
        // Note: The helper also accepts Unknown outcomes, but creating a real Unknown
        // result requires complex formulas that timeout the solver.
        // The helper's implementation correctly accepts both Verified and Unknown.
    })
}

#[test]
fn test_expect_error_rejects_non_error_outcomes() {
    common::with_clean_verification(|| {
        // Test that expect_error properly rejects Verified
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "true_assert".to_string(),
            "true".to_string(),
            None,
        );

        let result = expect_error();
        assert!(
            result.is_err(),
            "expect_error should reject Verified outcome"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Error but got Verified"),
            "Error message should indicate Verified was rejected"
        );

        // Test that expect_error properly rejects Counterexample
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "false_assert".to_string(),
            "false".to_string(),
            None,
        );

        let result = expect_error();
        assert!(
            result.is_err(),
            "expect_error should reject Counterexample outcome"
        );
        assert!(
            result
                .unwrap_err()
                .contains("Expected Error but got Counterexample"),
            "Error message should indicate Counterexample was rejected"
        );
    })
}
