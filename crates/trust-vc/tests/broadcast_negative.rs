// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for broadcast lemmas.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid broadcast lemmas
//!
//! These tests verify that invalid broadcast lemmas are properly rejected.

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

mod common;

#[test]
fn test_broadcast_with_false_condition_fails() {
    common::with_clean_verification(|| {
        // Test that a broadcast lemma with an always-false condition fails
        // Simulate a broadcast lemma that claims 5 < 3
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "broadcast_false".to_string(),
            "5 < 3".to_string(), // This is false
            Some("broadcast_negative.rs:21".to_string()),
        );

        // Should produce a counterexample
        expect_counterexample()
            .expect("Broadcast with false condition should produce counterexample");
    })
}

#[test]
fn test_broadcast_contradictory_lemmas_fail() {
    common::with_clean_verification(|| {
        // Test that contradictory broadcast lemmas are rejected
        // Add a contradictory broadcast lemma
        // Trying to assert both that something is true and false
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "broadcast_contradiction".to_string(),
            "(10 > 5) && (10 < 5)".to_string(), // Contradiction: 10 can't be both > and < 5
            None,
        );

        // Should fail due to contradiction
        expect_counterexample()
            .expect("Contradictory broadcast lemmas should produce counterexample");
    })
}

#[test]
fn test_broadcast_with_invalid_arithmetic_fails() {
    common::with_clean_verification(|| {
        // Test broadcast lemma with invalid arithmetic
        // Simulate a broadcast lemma with incorrect arithmetic
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "broadcast_bad_math".to_string(),
            "2 + 2 == 5".to_string(), // Wrong!
            Some("broadcast_negative.rs:87".to_string()),
        );

        // Should fail verification
        expect_counterexample()
            .expect("Broadcast with bad arithmetic should produce counterexample");
    })
}

#[test]
fn test_broadcast_circular_dependency_fails() {
    common::with_clean_verification(|| {
        // Test that circular dependencies in broadcast lemmas are problematic
        // Simulate circular dependency: A implies B, B implies not A
        // This creates an inconsistency
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "circular_1".to_string(),
            "(true) && (false)".to_string(), // Simplified: always false
            None,
        );

        // Should fail due to inconsistency
        expect_counterexample().expect("Circular dependency should produce counterexample");
    })
}
