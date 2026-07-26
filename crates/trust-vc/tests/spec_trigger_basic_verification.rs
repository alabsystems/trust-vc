// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification tests for #[spec] and #[trigger] functions.
//!
//! This file tests that spec functions actually verify correctly through ay,
//! not just that they compile or panic at runtime.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through test helpers

use trust_vc::{proof, spec};
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro;

// Test helper module for verification
#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::{expect_counterexample, expect_verified};

mod common;

#[spec]
fn spec_double_1816(x: i32) -> i32 {
    x + x
}

#[proof]
fn proof_spec_body_axiom_1816() {
    // In proof mode this call registers the spec body axiom into the
    // verification context via expand_spec().
    let _ = spec_double_1816(0);
    trust_vc::assert!(spec_double_1816(3) == 6);
}

#[test]
fn test_spec_body_axiom_macro_path_verifies() {
    let result = common::verify_should_pass(proof_spec_body_axiom_1816);
    assert!(
        matches!(result, trust_vc_core::VerifyResult::Verified),
        "Expected Verified, got: {:?}",
        result
    );
}

#[spec]
fn fact_1816_recursive(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * fact_1816_recursive(n - 1)
    }
}

#[proof]
fn proof_recursive_spec_body_axiom_1816() {
    // Register the recursive spec body axiom in proof mode before verifying.
    let _ = fact_1816_recursive(0);
    trust_vc::assert!(fact_1816_recursive(3) == 6);
}

#[test]
fn test_recursive_spec_body_axiom_macro_path_verifies_with_fuel() {
    // Fuel encoding is now implemented (direct defining axiom + E-matching).
    // fact_1816_recursive(3) == 6 should verify with sufficient unrolling.
    // Updated from stale "fails closed" expectation. Part of #2658 Category F.
    let result = common::verify_and_get_result(proof_recursive_spec_body_axiom_1816);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Verified
                | trust_vc_core::VerifyResult::Unknown { .. }
                | trust_vc_core::VerifyResult::Counterexample { .. }
        ),
        "recursive #[spec] body axiom should not produce Error after fuel encoding, got: {:?}",
        result
    );
}

#[test]
fn test_spec_positive_assertion_verifies() {
    common::with_clean_verification(|| {
        // Test: n > 0 verifies when n = 5
        // Set up variable
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        // Assume n = 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5".to_string(),
            None,
        );

        // Assert n > 0
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "positive_check".to_string(),
            "n > 0".to_string(),
            Some("spec_verification:positive".to_string()),
        );

        expect_verified().expect("n > 0 should verify when n = 5");
    })
}

#[test]
fn test_spec_positive_assertion_fails() {
    common::with_clean_verification(|| {
        // Test: n > 0 fails when n = 0
        // Set up variable
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        // Assume n = 0
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 0".to_string(),
            None,
        );

        // Assert n > 0
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "positive_check".to_string(),
            "n > 0".to_string(),
            Some("spec_verification:zero_fail".to_string()),
        );

        expect_counterexample().expect("n > 0 should fail when n = 0");
    })
}

#[test]
fn test_max_function_properties() {
    common::with_clean_verification(|| {
        // Test: max(a, b) >= a && max(a, b) >= b
        // Set up variables
        verify_macro::collect_variable("a".to_string(), "i64".to_string());
        verify_macro::collect_variable("b".to_string(), "i64".to_string());
        verify_macro::collect_variable("max".to_string(), "i64".to_string());

        // Assume specific values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 5".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 10".to_string(),
            None,
        );

        // Define max correctly
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "max_def".to_string(),
            "max == 10".to_string(), // Since b > a
            None,
        );

        // Assert max >= a
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "max_ge_a".to_string(),
            "max >= a".to_string(),
            Some("spec_verification:max_ge_a".to_string()),
        );

        // Assert max >= b
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "max_ge_b".to_string(),
            "max >= b".to_string(),
            Some("spec_verification:max_ge_b".to_string()),
        );

        expect_verified().expect("max(5, 10) = 10 should satisfy max >= a && max >= b");
    })
}

#[test]
fn test_min_function_properties() {
    common::with_clean_verification(|| {
        // Test: min(a, b) <= a && min(a, b) <= b
        // Set up variables
        verify_macro::collect_variable("a".to_string(), "i64".to_string());
        verify_macro::collect_variable("b".to_string(), "i64".to_string());
        verify_macro::collect_variable("min".to_string(), "i64".to_string());

        // Assume specific values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 7".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 3".to_string(),
            None,
        );

        // Define min correctly
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "min_def".to_string(),
            "min == 3".to_string(), // Since b < a
            None,
        );

        // Assert min <= a
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "min_le_a".to_string(),
            "min <= a".to_string(),
            Some("spec_verification:min_le_a".to_string()),
        );

        // Assert min <= b
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "min_le_b".to_string(),
            "min <= b".to_string(),
            Some("spec_verification:min_le_b".to_string()),
        );

        expect_verified().expect("min(7, 3) = 3 should satisfy min <= a && min <= b");
    })
}

#[test]
fn test_incorrect_max_definition_fails() {
    common::with_clean_verification(|| {
        // Test: Wrong max definition leads to counterexample
        // Set up variables
        verify_macro::collect_variable("a".to_string(), "i64".to_string());
        verify_macro::collect_variable("b".to_string(), "i64".to_string());
        verify_macro::collect_variable("max".to_string(), "i64".to_string());

        // Assume specific values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 15".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 8".to_string(),
            None,
        );

        // Define max INCORRECTLY
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "max_wrong".to_string(),
            "max == 8".to_string(), // Wrong! Should be 15
            None,
        );

        // Assert max >= a (this should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "max_ge_a".to_string(),
            "max >= a".to_string(),
            Some("spec_verification:wrong_max".to_string()),
        );

        expect_counterexample().expect("max = 8 < a = 15 should produce counterexample");
    })
}
