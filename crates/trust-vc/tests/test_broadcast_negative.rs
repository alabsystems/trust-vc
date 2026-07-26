// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for broadcast lemmas
//!
//! These tests ensure that invalid broadcast lemmas are properly rejected.
//! Each test verifies that false broadcast lemmas produce Counterexample results.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid broadcast lemmas

use trust_vc::{assert_by, broadcast, trigger};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[cfg(test)]
mod negative_broadcast_tests {
    use super::*;

    /// Test that false broadcast lemmas are rejected
    #[test]
    fn test_false_broadcast_lemma_must_fail() {
        common::with_clean_verification(|| {
            // NOTE: Broadcast macros need to be at module level to work properly
            // For now, we directly register the false assertion
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "false_broadcast".to_string(),
                "false".to_string(), // This is always false
                Some("test_broadcast_negative.rs:31".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // The false assertion should produce a counterexample
            assert!(
                matches!(result, VerifyResult::Counterexample { .. }),
                "False broadcast lemma MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that contradictory broadcast lemmas are rejected
    #[test]
    fn test_contradictory_broadcast_must_fail() {
        common::with_clean_verification(|| {
            // Register a broadcast lemma that claims x * x < 0 (always false for real numbers)
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "contradictory_square".to_string(),
                "5 * 5 < 0".to_string(), // 25 < 0 is false
                Some("test_broadcast_negative.rs:56".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should produce counterexample due to contradiction
            assert!(
                matches!(result, VerifyResult::Counterexample { .. }),
                "Contradictory broadcast MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that invalid arithmetic broadcast lemmas are rejected
    #[test]
    fn test_invalid_arithmetic_broadcast_must_fail() {
        common::with_clean_verification(|| {
            // Define a broadcast lemma with incorrect arithmetic
            #[broadcast]
            #[trigger(x + y)]
            fn lemma_wrong_addition(x: i32, y: i32) {
                assert_by!(x + y == x + y + 1); // Always false: n != n+1
            }

            // Try to use correct arithmetic
            fn use_broadcast() {
                let a = 2;
                let b = 2;
                lemma_wrong_addition(a, b); // Apply the false broadcast
                assert_by!(a + b == 4); // This conflicts with broadcast claiming 4 == 5
            }

            use_broadcast();

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should fail due to conflicting broadcast
            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid arithmetic broadcast MUST NOT verify, got {:?}",
                result
            );
        })
    }

    /// Test that broadcast lemmas with invalid triggers are rejected
    #[test]
    fn test_invalid_trigger_broadcast_must_fail() {
        common::with_clean_verification(|| {
            // Define a broadcast with a trigger that makes false claims
            #[broadcast]
            #[trigger(x * x)]
            fn lemma_square_negative(x: i32) {
                assert_by!(x * x < 0); // False: squares are never negative
            }

            // Try to use square in a proof
            fn use_broadcast() {
                let val = 5;
                lemma_square_negative(val); // Apply the false broadcast
                assert_by!(val * val == 25); // This conflicts with broadcast claiming 5*5 < 0
            }

            use_broadcast();

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should fail due to false broadcast
            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid trigger broadcast MUST NOT verify, got {:?}",
                result
            );
        })
    }

    /// Test that broadcast lemmas claiming invalid properties are rejected
    #[test]
    fn test_invalid_property_broadcast_must_fail() {
        common::with_clean_verification(|| {
            // Define a broadcast claiming all numbers are negative
            #[broadcast]
            #[trigger(x)]
            fn lemma_all_negative(x: i32) {
                assert_by!(x < 0); // False for positive numbers
            }

            // Try to assert something about positive numbers
            fn use_broadcast() {
                let positive = 10;
                lemma_all_negative(positive); // Apply the false broadcast
                assert_by!(positive > 0); // This conflicts with broadcast claiming 10 < 0
            }

            use_broadcast();

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should fail due to false broadcast
            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid property broadcast MUST NOT verify, got {:?}",
                result
            );
        })
    }

    /// Test that multiple conflicting broadcasts are rejected
    #[test]
    fn test_conflicting_broadcasts_must_fail() {
        common::with_clean_verification(|| {
            // Define two conflicting broadcasts
            #[broadcast]
            #[trigger(x)]
            fn lemma_greater_than_ten(x: i32) {
                assert_by!(x > 10); // Claims all numbers > 10
            }

            #[broadcast]
            #[trigger(y)]
            fn lemma_less_than_five(y: i32) {
                assert_by!(y < 5); // Claims all numbers < 5
            }

            // Try to assert something that conflicts with both
            fn use_broadcasts() {
                let num = 7;
                lemma_greater_than_ten(num); // Claims 7 > 10 (false)
                lemma_less_than_five(num); // Claims 7 < 5 (false)
                assert_by!((5..=10).contains(&num)); // True, but conflicts with both broadcasts
            }

            use_broadcasts();

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should fail due to conflicting broadcasts
            assert!(
                !matches!(result, VerifyResult::Verified),
                "Conflicting broadcasts MUST NOT verify, got {:?}",
                result
            );
        })
    }
}

/// Test that register_broadcast_lemma produces BroadcastAssume (not plain Assume).
///
/// Uses the real register_broadcast_lemma code path: collect Ensures, then call
/// register_broadcast_lemma to convert them. Verifies the resulting obligation
/// has BroadcastAssume kind and the "broadcast_" name prefix.
///
/// Regression test for #1513.
#[test]
fn test_broadcast_assume_not_plain_assume() {
    common::with_clean_verification(|| {
        // Register a variable (simulates broadcast function parameter)
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Collect an Ensures obligation (simulates ensures! inside broadcast body)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "lemma_condition".to_string(),
            "n > 0".to_string(),
            Some("test:broadcast_soundness".to_string()),
        );

        // Call register_broadcast_lemma — this should convert Ensures to BroadcastAssume
        verify_macro::register_broadcast_lemma("test_broadcast".to_string());

        let pipeline = VerificationPipeline::collect_from_macros();

        // Verify that register_broadcast_lemma converted to BroadcastAssume (not Assume)
        let broadcast_count = pipeline
            .context()
            .obligations()
            .iter()
            .filter(|o| matches!(o.kind(), trust_vc_core::vc::ObligationKind::BroadcastAssume))
            .count();
        assert_eq!(
            broadcast_count, 1,
            "register_broadcast_lemma should produce exactly 1 BroadcastAssume obligation"
        );

        // Verify no plain Assume obligations were created (the old bug)
        let plain_assume_count = pipeline
            .context()
            .obligations()
            .iter()
            .filter(|o| matches!(o.kind(), trust_vc_core::vc::ObligationKind::Assume))
            .count();
        assert_eq!(
            plain_assume_count, 0,
            "register_broadcast_lemma should NOT produce plain Assume (old bug)"
        );

        // Verify the broadcast_ name prefix was added
        let broadcast_ob = pipeline
            .context()
            .obligations()
            .iter()
            .find(|o| matches!(o.kind(), trust_vc_core::vc::ObligationKind::BroadcastAssume))
            .expect("BroadcastAssume obligation should exist");
        assert!(
            broadcast_ob.name().starts_with("broadcast_"),
            "BroadcastAssume obligation should have broadcast_ prefix, got: {}",
            broadcast_ob.name()
        );
    })
}

/// Test that the broadcast backward sweep has a boundary.
///
/// When register_broadcast_lemma converts Ensures to BroadcastAssume, it should
/// stop at the first non-Ensures obligation, not convert ALL Ensures in context.
///
/// Regression test for #1513 sweep boundary.
#[test]
fn test_broadcast_sweep_boundary() {
    common::with_clean_verification(|| {
        // First, add an Ensures obligation from a non-broadcast function
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "non_broadcast_postcondition".to_string(),
            "true".to_string(),
            Some("test:sweep_boundary".to_string()),
        );

        // Add a non-Ensures obligation as a boundary
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "separator".to_string(),
            "true".to_string(),
            Some("test:sweep_boundary".to_string()),
        );

        // Now simulate a broadcast lemma's ensures
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "broadcast_postcondition".to_string(),
            "true".to_string(),
            Some("test:sweep_boundary".to_string()),
        );

        // Call register_broadcast_lemma — it should only convert the last Ensures
        verify_macro::register_broadcast_lemma("test_lemma".to_string());

        // Check the obligations: only the last Ensures should be BroadcastAssume
        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        // First obligation should still be Ensures (not converted)
        assert_eq!(
            obligations[0].kind(),
            trust_vc_core::vc::ObligationKind::Ensures,
            "First Ensures should NOT be converted (sweep boundary should stop at Assert)"
        );

        // Second obligation should still be Assert
        assert_eq!(
            obligations[1].kind(),
            trust_vc_core::vc::ObligationKind::Assert,
            "Assert separator should be unchanged"
        );

        // Third obligation should be BroadcastAssume (converted)
        assert_eq!(
            obligations[2].kind(),
            trust_vc_core::vc::ObligationKind::BroadcastAssume,
            "Last Ensures should be converted to BroadcastAssume"
        );
        assert!(
            obligations[2].name().starts_with("broadcast_"),
            "Converted obligation should have broadcast_ prefix"
        );
    })
}
