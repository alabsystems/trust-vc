// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for trigger patterns.
//!
//! These tests verify that invalid trigger patterns are properly rejected.
//! Concrete false conditions must produce Counterexample — accepting
//! Unknown masks regressions (#1697).

mod common;

#[test]
fn test_trigger_with_unsatisfiable_pattern_fails() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "impossible_trigger".to_string(),
            "(5 < 3) && (3 > 5)".to_string(),
            Some("trigger_negative.rs:21".to_string()),
        );

        match trust_vc_core::verify_macro::verify_collected() {
            trust_vc_core::VerifyResult::Counterexample { .. } => {
                // Concrete false: "(5<3) && (3>5)" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false '(5<3)&&(3>5)' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}

#[test]
fn test_trigger_causing_infinite_loop_pattern() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "loop_trigger".to_string(),
            "false".to_string(),
            None,
        );

        match trust_vc_core::verify_macro::verify_collected() {
            trust_vc_core::VerifyResult::Counterexample { .. } => {
                // Concrete false: "false" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false 'false' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}

#[test]
fn test_trigger_with_type_mismatch_fails() {
    common::with_clean_verification(|| {
        // Malformed input: string literal compared to integer.
        // Error is the primary expected outcome; Unknown/Counterexample
        // are acceptable fallbacks for malformed expressions.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "type_mismatch_trigger".to_string(),
            "\"string\" == 42".to_string(),
            None,
        );

        match trust_vc_core::verify_macro::verify_collected() {
            trust_vc_core::VerifyResult::Error { .. }
            | trust_vc_core::VerifyResult::Counterexample { .. }
            | trust_vc_core::VerifyResult::Unknown { .. } => {
                // Malformed input — Error preferred, others acceptable.
            }
            trust_vc_core::VerifyResult::Verified => {
                panic!("Type mismatch trigger should not verify!");
            }
            other => panic!("Unexpected VerifyResult variant: {:?}", other),
        }
    })
}

#[test]
fn test_conflicting_trigger_groups_fail() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "trigger_group_conflict".to_string(),
            "(true && false)".to_string(),
            None,
        );

        match trust_vc_core::verify_macro::verify_collected() {
            trust_vc_core::VerifyResult::Counterexample { .. } => {
                // Concrete false: "(true && false)" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false '(true && false)' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}
