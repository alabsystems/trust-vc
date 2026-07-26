// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification tests for broadcast lemmas and trigger patterns.
//!
//! Tests that broadcast lemmas and triggers work correctly in verification.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through test helpers

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro;

// Test helper module for verification
#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::{expect_counterexample, expect_verified};

mod common;

#[test]
fn test_broadcast_lemma_auto_application() {
    common::with_clean_verification(|| {
        // Discriminatory: succ_x is unconstrained — broadcast is the sole info source.
        // Without the broadcast assumption, succ_x == 6 is unprovable.
        // succ_x represents an uninterpreted function application succ(x).
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("succ_x".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );

        // Broadcast: succ_x == x + 1 (succ_x is unconstrained without this)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "broadcast_succ".to_string(),
            "succ_x == x + 1".to_string(),
            Some("broadcast:succ_def".to_string()),
        );

        // Assert: succ_x == 6 — requires broadcast (x=5, so succ_x == 5+1 == 6)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "succ_result".to_string(),
            "succ_x == 6".to_string(),
            Some("test_broadcast:succ_check".to_string()),
        );

        expect_verified()
            .expect("Broadcast succ_x == x + 1 should make succ_x == 6 provable when x == 5");
    })
}

#[test]
fn test_trigger_pattern_matching() {
    common::with_clean_verification(|| {
        // Discriminatory: bounds_ok is unconstrained — trigger assumption is sole info.
        // Without the trigger assumption, bounds_ok == 1 is unprovable.
        // bounds_ok represents an uninterpreted in_bounds(i, n) application.
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("n".to_string(), "i32".to_string());
        verify_macro::collect_variable("bounds_ok".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "i_value".to_string(),
            "i == 3".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 10".to_string(),
            None,
        );

        // Trigger: when 0 <= i < n, bounds_ok == 1
        // bounds_ok is unconstrained without this assumption
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "trigger_bounds".to_string(),
            "!(0 <= i && i < n) || bounds_ok == 1".to_string(),
            Some("trigger:bounds_check".to_string()),
        );

        // Assert: bounds_ok == 1 — requires trigger (i=3, n=10, so 0<=3<10)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "bounds_valid".to_string(),
            "bounds_ok == 1".to_string(),
            Some("test_trigger:bounds_check".to_string()),
        );

        expect_verified().expect("Trigger should prove bounds_ok == 1 when 0 <= i < n holds");
    })
}

#[test]
fn test_multiple_triggers_on_same_lemma() {
    common::with_clean_verification(|| {
        // Discriminatory: combined is unconstrained — multi-trigger assumption is sole info.
        // Without the assumption, combined == 10 is unprovable.
        // combined represents an uninterpreted combine(a, b) application.
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());
        verify_macro::collect_variable("combined".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 3".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 7".to_string(),
            None,
        );

        // Multi-trigger lemma: combined == a + b (combined is unconstrained without this)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "multi_trigger_combine".to_string(),
            "combined == a + b".to_string(),
            Some("trigger:combine_def".to_string()),
        );

        // Assert: combined == 10 — requires trigger (a=3, b=7, so combined == 3+7 == 10)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "combine_result".to_string(),
            "combined == 10".to_string(),
            Some("test_multi_trigger:combine_check".to_string()),
        );

        expect_verified().expect("Multi-trigger lemma should prove combined == 10 when a=3, b=7");
    })
}

#[test]
fn test_broadcast_lemma_not_triggered() {
    common::with_clean_verification(|| {
        // Test that broadcast lemmas don't apply when trigger conditions aren't met
        // Set up variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume values where x >= y (trigger condition not met)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 10".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 5".to_string(),
            None,
        );

        // Broadcast lemma only applies when x < y
        // Since x >= y, the lemma shouldn't help us
        // Using NOT(antecedent) OR consequent instead of ==>
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "broadcast_lemma".to_string(),
            "!(x < y) || (x + 1 <= y)".to_string(),
            Some("broadcast:conditional_lemma".to_string()),
        );

        // Try to assert x + 1 <= y (should fail since 11 > 5)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "false_claim".to_string(),
            "x + 1 <= y".to_string(),
            Some("test_not_triggered:false".to_string()),
        );

        expect_counterexample().expect("Without trigger condition met, x + 1 <= y should fail");
    })
}
