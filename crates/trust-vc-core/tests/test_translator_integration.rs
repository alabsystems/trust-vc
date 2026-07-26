//! Tests for Rust-to-SMT translator integration.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

#[test]
fn test_translator_handles_logical_operators() {
    // Test that Rust && and || are translated to SMT and/or.
    // Variables are bounded to avoid BV32 overflow: x + y must fit in i32.
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("x".to_string(), "i32".to_string());
        collect_variable("y".to_string(), "i32".to_string());

        // Add assumption using Rust syntax — bound values to prevent BV overflow
        collect_obligation(
            ObligationKind::Assume,
            "both_positive_bounded".to_string(),
            "x > 0 && x < 1000 && y > 0 && y < 1000".to_string(),
            None,
        );

        // Add assertion using Rust syntax
        collect_obligation(
            ObligationKind::Assert,
            "sum_positive".to_string(),
            "x + y > 0".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Logical operators should be translated and verify: {:?}",
            result
        );
    })
}

#[test]
fn test_translator_handles_negation() {
    // Test that Rust ! is translated to SMT not
    common::with_clean_verification(|| {
        // Declare variable
        collect_variable("flag".to_string(), "bool".to_string());

        // Add assumption using Rust syntax
        collect_obligation(
            ObligationKind::Assume,
            "flag_true".to_string(),
            "flag".to_string(),
            None,
        );

        // Add assertion using Rust negation
        collect_obligation(
            ObligationKind::Assert,
            "not_not_flag".to_string(),
            "!!flag".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Negation should be translated and verify: {:?}",
            result
        );
    })
}

#[test]
fn test_translator_fallback_on_unsupported() {
    // Test that unsupported Rust syntax falls back gracefully
    common::with_clean_verification(|| {
        // Declare variable
        collect_variable("x".to_string(), "i32".to_string());

        // Try to use unsupported syntax (should fall back to original)
        // This won't verify correctly, but shouldn't crash
        collect_obligation(
            ObligationKind::Assume,
            "test".to_string(),
            "x.some_unknown_method()".to_string(),
            None,
        );

        // Add a simple assertion to have something to verify
        collect_obligation(
            ObligationKind::Assert,
            "trivial".to_string(),
            "true".to_string(),
            None,
        );

        // Should not panic, even if verification fails
        let _ = verify_collected();
    })
}

#[test]
fn test_translator_complex_expression() {
    // Test a more complex expression with multiple variables and operators.
    // Variables are bounded to prevent BV32 overflow in sums.
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("a".to_string(), "i32".to_string());
        collect_variable("b".to_string(), "i32".to_string());
        collect_variable("c".to_string(), "i32".to_string());

        // Add assumptions — bound values to prevent BV overflow in a+b and b+c
        collect_obligation(
            ObligationKind::Assume,
            "a_pos_bounded".to_string(),
            "a > 0 && a < 1000".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Assume,
            "b_pos_bounded".to_string(),
            "b > 0 && b < 1000".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Assume,
            "c_pos_bounded".to_string(),
            "c > 0 && c < 1000".to_string(),
            None,
        );

        // Complex assertion with parentheses and multiple operators
        collect_obligation(
            ObligationKind::Assert,
            "complex".to_string(),
            "(a + b) > 0 && (b + c) > 0".to_string(),
            None,
        );

        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Complex expressions should translate and verify: {:?}",
            result
        );
    })
}
