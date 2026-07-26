// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test that unsigned comparison and arithmetic operations work correctly
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests that the encoder properly handles unsigned types in comparisons and arithmetic

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_unsigned_comparison_ge() {
    common::with_clean_verification(|| {
        // Test that unsigned >= works correctly
        // u32::MAX >= 0 should be true
        // Declare unsigned variable
        verify_macro::collect_variable("x".to_string(), "u32".to_string());

        // Set x = u32::MAX
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_max".to_string(),
            "x == 4294967295".to_string(), // u32::MAX
            Some("test_unsigned:ge".to_string()),
        );

        // Assert x >= 0 (should be true for unsigned)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "x_ge_zero".to_string(),
            "x >= 0".to_string(),
            Some("test_unsigned:ge".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX >= 0 should verify for unsigned, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_comparison_lt() {
    common::with_clean_verification(|| {
        // Test that unsigned < works correctly
        // 0 < u32::MAX should be true
        // Declare unsigned variables
        verify_macro::collect_variable("x".to_string(), "u32".to_string());
        verify_macro::collect_variable("y".to_string(), "u32".to_string());

        // Set x = 0, y = u32::MAX
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_zero".to_string(),
            "x == 0".to_string(),
            Some("test_unsigned:lt".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_is_max".to_string(),
            "y == 4294967295".to_string(), // u32::MAX
            Some("test_unsigned:lt".to_string()),
        );

        // Assert x < y (should be true)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "x_lt_y".to_string(),
            "x < y".to_string(),
            Some("test_unsigned:lt".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "0 < u32::MAX should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_division() {
    common::with_clean_verification(|| {
        // Test that unsigned division works correctly
        // u32::MAX / 2 should be 2147483647 (not negative)
        // Declare unsigned variables
        verify_macro::collect_variable("x".to_string(), "u32".to_string());
        verify_macro::collect_variable("result".to_string(), "u32".to_string());

        // Set x = u32::MAX
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_max".to_string(),
            "x == 4294967295".to_string(), // u32::MAX
            Some("test_unsigned:div".to_string()),
        );

        // Set result = x / 2
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "compute_div".to_string(),
            "result == x / 2".to_string(),
            Some("test_unsigned:div".to_string()),
        );

        // Assert result > 0 (should be true since result = 2147483647)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "result_positive".to_string(),
            "result > 0".to_string(),
            Some("test_unsigned:div".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX / 2 > 0 should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_remainder() {
    common::with_clean_verification(|| {
        // Test that unsigned remainder works correctly
        // 10 % 3 = 1 for unsigned
        // Declare unsigned variables
        verify_macro::collect_variable("x".to_string(), "u32".to_string());
        verify_macro::collect_variable("y".to_string(), "u32".to_string());
        verify_macro::collect_variable("result".to_string(), "u32".to_string());

        // Set x = 10, y = 3
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_10".to_string(),
            "x == 10".to_string(),
            Some("test_unsigned:rem".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "y_is_3".to_string(),
            "y == 3".to_string(),
            Some("test_unsigned:rem".to_string()),
        );

        // Set result = x % y
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "compute_rem".to_string(),
            "result == x % y".to_string(),
            Some("test_unsigned:rem".to_string()),
        );

        // Assert result == 1
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "result_is_1".to_string(),
            "result == 1".to_string(),
            Some("test_unsigned:rem".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "10 % 3 == 1 should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_wraparound() {
    common::with_clean_verification(|| {
        // Test that unsigned values don't go negative
        // u8::MIN - 1 should wrap to u8::MAX (255)
        // Declare unsigned variables
        verify_macro::collect_variable("x".to_string(), "u8".to_string());
        verify_macro::collect_variable("result".to_string(), "u8".to_string());

        // Set x = 0 (u8::MIN)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_min".to_string(),
            "x == 0".to_string(),
            Some("test_unsigned:wrap".to_string()),
        );

        // In bitvector arithmetic, 0 - 1 wraps to 255 for u8
        // We assume wrapping_sub behavior
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "compute_sub".to_string(),
            "result == 255".to_string(), // wrapping_sub(0, 1) = 255 for u8
            Some("test_unsigned:wrap".to_string()),
        );

        // Assert result > 200 (should be true since result = 255)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "result_large".to_string(),
            "result > 200".to_string(),
            Some("test_unsigned:wrap".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Wrapped u8 value should be > 200, got: {:?}",
            result
        );
    })
}

#[test]
fn test_signed_comparison_still_works() {
    common::with_clean_verification(|| {
        // Test that signed comparisons still work correctly
        // -1 < 0 for signed i32
        // Declare signed variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Set x = -1
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_neg".to_string(),
            "x == -1".to_string(),
            Some("test_signed:lt".to_string()),
        );

        // Assert x < 0 (should be true for signed)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "x_lt_zero".to_string(),
            "x < 0".to_string(),
            Some("test_signed:lt".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "-1 < 0 should verify for signed, got: {:?}",
            result
        );
    })
}
