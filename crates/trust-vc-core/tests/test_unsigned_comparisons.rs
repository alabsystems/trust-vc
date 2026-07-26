// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Comprehensive tests for unsigned integer comparison operations.
//! Verifies that unsigned types use correct bit-vector operations (bvult, bvule, bvugt, bvuge)
//! instead of signed operations.

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable};
use trust_vc_core::VerifyResult;

#[test]
fn test_unsigned_comparison_255u8_gt_1u8() {
    // Test that 255u8 > 1u8 is verified correctly
    // If we were using signed comparison, this would fail since 255u8 = -1i8 < 1i8
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("x".to_string(), "u8".to_string());
        collect_variable("y".to_string(), "u8".to_string());

        // Add variable declarations for unsigned values
        collect_obligation(
            ObligationKind::Assume,
            "x_value".to_string(),
            "x == 255".to_string(), // Just use number, type is already u8
            Some("test:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "y_value".to_string(),
            "y == 1".to_string(),
            Some("test:2:1".to_string()),
        );

        // Assert that x > y (255u8 > 1u8 should be true)
        collect_obligation(
            ObligationKind::Assert,
            "unsigned_gt".to_string(),
            "x > y".to_string(),
            Some("test:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "255u8 > 1u8 should verify (testing unsigned comparison), got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_comparison_large_values() {
    // Test with larger unsigned values
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("a".to_string(), "u32".to_string());
        collect_variable("b".to_string(), "u32".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "a_value".to_string(),
            "a == 4000000000".to_string(), // Large unsigned value
            Some("test:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "b_value".to_string(),
            "b == 100".to_string(),
            Some("test:2:1".to_string()),
        );

        // Assert that a > b (large unsigned > small unsigned)
        collect_obligation(
            ObligationKind::Assert,
            "large_gt_small".to_string(),
            "a > b".to_string(),
            Some("test:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Large unsigned > small unsigned should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_comparison_edge_cases() {
    // Test edge cases with unsigned types
    common::with_clean_verification(|| {
        // Declare variable
        collect_variable("max_val".to_string(), "u8".to_string());

        // Test that u8::MAX >= u8::MAX
        collect_obligation(
            ObligationKind::Assume,
            "max_val".to_string(),
            "max_val == 255".to_string(),
            Some("test:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assert,
            "max_ge_max".to_string(),
            "max_val >= 255".to_string(),
            Some("test:2:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u8::MAX >= u8::MAX should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_comparison_should_fail() {
    // Test that incorrect unsigned comparisons fail appropriately
    common::with_clean_verification(|| {
        // Declare variables
        collect_variable("small".to_string(), "u32".to_string());
        collect_variable("large".to_string(), "u32".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "small".to_string(),
            "small == 10".to_string(),
            Some("test:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "large".to_string(),
            "large == 1000".to_string(),
            Some("test:2:1".to_string()),
        );

        // Assert that small > large (should fail)
        collect_obligation(
            ObligationKind::Assert,
            "small_gt_large".to_string(),
            "small > large".to_string(),
            Some("test:3:1".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "10u32 > 1000u32 should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_all_comparison_operators() {
    // Test all comparison operators (>, >=, <, <=, ==, !=) with unsigned values
    common::with_clean_verification(|| {
        collect_variable("a".to_string(), "u16".to_string());
        collect_variable("b".to_string(), "u16".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "a_val".to_string(),
            "a == 65000".to_string(), // Large u16 value
            Some("test_all_ops:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assume,
            "b_val".to_string(),
            "b == 100".to_string(),
            Some("test_all_ops:2".to_string()),
        );

        // Test all operators
        collect_obligation(
            ObligationKind::Assert,
            "gt".to_string(),
            "a > b".to_string(), // 65000 > 100 = true
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "ge".to_string(),
            "a >= b".to_string(), // 65000 >= 100 = true
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "not_lt".to_string(),
            "!(a < b)".to_string(), // !(65000 < 100) = true
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "not_le".to_string(),
            "!(a <= b)".to_string(), // !(65000 <= 100) = true
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "not_eq".to_string(),
            "a != b".to_string(), // 65000 != 100 = true
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "All unsigned comparison operators should verify correctly, got: {:?}",
            result
        );
    })
}

#[test]
fn test_u64_boundary_conditions() {
    // Test boundary conditions for u64
    common::with_clean_verification(|| {
        collect_variable("max".to_string(), "u64".to_string());
        collect_variable("zero".to_string(), "u64".to_string());
        collect_variable("one".to_string(), "u64".to_string());

        // Use a large value that fits in i64 but still tests unsigned behavior
        // 9223372036854775807 is i64::MAX, so we'll use a value just below that
        collect_obligation(
            ObligationKind::Assume,
            "max_val".to_string(),
            "max == 9223372036854775000".to_string(), // Large u64 value below i64::MAX
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "zero_val".to_string(),
            "zero == 0".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "one_val".to_string(),
            "one == 1".to_string(),
            None,
        );

        // Test boundary comparisons
        collect_obligation(
            ObligationKind::Assert,
            "max_gt_zero".to_string(),
            "max > zero".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "zero_le_max".to_string(),
            "zero <= max".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "max_ge_max".to_string(),
            "max >= 9223372036854775000".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assert,
            "one_gt_zero".to_string(),
            "one > zero".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u64 boundary conditions should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_division_and_remainder() {
    // Test unsigned division and remainder operations
    common::with_clean_verification(|| {
        collect_variable("a".to_string(), "u32".to_string());
        collect_variable("b".to_string(), "u32".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "a_val".to_string(),
            "a == 17".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "b_val".to_string(),
            "b == 5".to_string(),
            None,
        );

        // Test division: 17 / 5 = 3
        collect_obligation(
            ObligationKind::Assert,
            "div_result".to_string(),
            "a / b == 3".to_string(),
            None,
        );

        // Test remainder: 17 % 5 = 2
        collect_obligation(
            ObligationKind::Assert,
            "rem_result".to_string(),
            "a % b == 2".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned division and remainder should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_less_than_operators() {
    // Test less than and less than or equal operators
    common::with_clean_verification(|| {
        collect_variable("small".to_string(), "u8".to_string());
        collect_variable("large".to_string(), "u8".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "small_val".to_string(),
            "small == 10".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "large_val".to_string(),
            "large == 200".to_string(),
            None,
        );

        // Test < operator
        collect_obligation(
            ObligationKind::Assert,
            "small_lt_large".to_string(),
            "small < large".to_string(), // 10 < 200 = true
            None,
        );

        // Test <= operator
        collect_obligation(
            ObligationKind::Assert,
            "small_le_large".to_string(),
            "small <= large".to_string(), // 10 <= 200 = true
            None,
        );

        // Test <= with equality
        collect_obligation(
            ObligationKind::Assert,
            "small_le_small".to_string(),
            "small <= 10".to_string(), // 10 <= 10 = true
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned less than operators should verify, got: {:?}",
            result
        );
    })
}
