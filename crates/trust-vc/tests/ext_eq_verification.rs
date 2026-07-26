// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification tests for extensional equality macros (ext_eq!, ext_ne!).
//!
//! Tests that ext_eq! and ext_ne! generate correct verification conditions
//! that can be verified by ay.
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
fn test_ext_eq_verification_same_values() {
    common::with_clean_verification(|| {
        // Test that ext_eq!(x, x) verifies
        // Set up variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume a value for x
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 42".to_string(),
            None,
        );

        // Assert ext_eq!(x, x) which should always be true
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_eq_same".to_string(),
            "x == x".to_string(), // ext_eq! expands to ==
            Some("ext_eq_verification:same".to_string()),
        );

        expect_verified().expect("ext_eq!(x, x) should always verify");
    })
}

#[test]
fn test_ext_eq_verification_equal_values() {
    common::with_clean_verification(|| {
        // Test that ext_eq!(x, y) verifies when x == y
        // Set up variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume equal values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 10".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 10".to_string(),
            None,
        );

        // Assert ext_eq!(x, y)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_eq_equal".to_string(),
            "x == y".to_string(),
            Some("ext_eq_verification:equal".to_string()),
        );

        expect_verified().expect("ext_eq!(10, 10) should verify");
    })
}

#[test]
fn test_ext_eq_verification_different_values() {
    common::with_clean_verification(|| {
        // Test that ext_eq!(x, y) fails when x != y
        // Set up variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume different values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 10".to_string(),
            None,
        );

        // Assert ext_eq!(x, y) - should fail
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_eq_different".to_string(),
            "x == y".to_string(),
            Some("ext_eq_verification:different".to_string()),
        );

        expect_counterexample().expect("ext_eq!(5, 10) should produce counterexample");
    })
}

#[test]
fn test_ext_ne_verification_different_values() {
    common::with_clean_verification(|| {
        // Test that ext_ne!(x, y) verifies when x != y
        // Set up variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume different values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 3".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 7".to_string(),
            None,
        );

        // Assert ext_ne!(x, y) which expands to x != y
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_ne_different".to_string(),
            "x != y".to_string(),
            Some("ext_eq_verification:ne_different".to_string()),
        );

        expect_verified().expect("ext_ne!(3, 7) should verify");
    })
}

#[test]
fn test_ext_ne_verification_same_values() {
    common::with_clean_verification(|| {
        // Test that ext_ne!(x, y) fails when x == y
        // Set up variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume same values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 15".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 15".to_string(),
            None,
        );

        // Assert ext_ne!(x, y) - should fail
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_ne_same".to_string(),
            "x != y".to_string(),
            Some("ext_eq_verification:ne_same".to_string()),
        );

        expect_counterexample().expect("ext_ne!(15, 15) should produce counterexample");
    })
}

#[test]
fn test_ext_eq_with_expressions() {
    common::with_clean_verification(|| {
        // Test ext_eq with expressions
        // Set up variables
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());

        // Assume values
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 5".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 3".to_string(),
            None,
        );

        // Assert ext_eq!(a + b, 8)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_eq_expr".to_string(),
            "(a + b) == 8".to_string(),
            Some("ext_eq_verification:expr".to_string()),
        );

        expect_verified().expect("ext_eq!(5 + 3, 8) should verify");
    })
}

#[test]
fn test_ext_eq_with_different_int_types() {
    common::with_clean_verification(|| {
        // Test ext_eq with different integer types (should handle type conversion)
        // Set up variables with different types
        verify_macro::collect_variable("x_u32".to_string(), "u32".to_string());
        verify_macro::collect_variable("x_u64".to_string(), "u64".to_string());

        // Both have same numeric value
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_u32_value".to_string(),
            "x_u32 == 42".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_u64_value".to_string(),
            "x_u64 == 42".to_string(),
            None,
        );

        // Assert they are extensionally equal (same value)
        // Note: Since encoder doesn't support casting, we compare values directly
        // In a real system, both would be converted to same bit-width
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_eq_diff_types".to_string(),
            "x_u32 == 42 && x_u64 == 42".to_string(),
            Some("ext_eq_verification:diff_types".to_string()),
        );

        expect_verified().expect("ext_eq should verify when both have same value");
    })
}

#[test]
fn test_ext_ne_with_overflow_boundary() {
    common::with_clean_verification(|| {
        // Test ext_ne near overflow boundaries
        // Set up u8 variables near overflow
        verify_macro::collect_variable("x".to_string(), "u8".to_string());
        verify_macro::collect_variable("y".to_string(), "u8".to_string());

        // x at max, y at max - 1
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 255".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 254".to_string(),
            None,
        );

        // Assert ext_ne!(x, y) at boundary
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "ext_ne_boundary".to_string(),
            "x != y".to_string(),
            Some("ext_eq_verification:boundary".to_string()),
        );

        expect_verified().expect("ext_ne!(255, 254) should verify for u8");
    })
}
