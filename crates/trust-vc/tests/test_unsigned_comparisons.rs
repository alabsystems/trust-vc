// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test for issue #1249 - unsigned comparison type tracking

use trust_vc::assert_by;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_unsigned_variable_on_right() {
    common::with_clean_verification(|| {
        // Declare the variable to the verification context
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        // Add assumption about the value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5".to_string(),
            None,
        );

        let n: u64 = 5;

        // This should use unsigned comparison since n is u64
        // Previously would fail because only checked current_receiver_name
        assert_by!(0 < n);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned comparison with variable on right should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_complex_expression() {
    common::with_clean_verification(|| {
        // Declare the variables to the verification context
        verify_macro::collect_variable("a".to_string(), "u64".to_string());
        verify_macro::collect_variable("b".to_string(), "u64".to_string());

        // Add assumptions about the values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_value".to_string(),
            "a == 10".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_value".to_string(),
            "b == 5".to_string(),
            None,
        );

        let a: u64 = 10;
        let b: u64 = 5;

        // Complex expression with unsigned types
        assert_by!(a + b < 100);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned comparison with complex expression should verify, got {:?}",
            result
        );
    })
}

#[test]
fn test_signed_vs_unsigned_comparison() {
    common::with_clean_verification(|| {
        // Declare the variables to the verification context
        verify_macro::collect_variable("signed".to_string(), "i32".to_string());
        verify_macro::collect_variable("unsigned".to_string(), "u32".to_string());

        // Add assumptions about the values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "signed_value".to_string(),
            "signed == -5".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "unsigned_value".to_string(),
            "unsigned == 10".to_string(),
            None,
        );

        let signed: i32 = -5;
        let unsigned: u32 = 10;

        // Test that we properly handle signed types
        assert_by!(signed < 0);

        // Separate unsigned comparison
        assert_by!(unsigned > 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Mixed signed/unsigned comparisons should verify correctly, got {:?}",
            result
        );
    })
}

#[test]
#[allow(clippy::absurd_extreme_comparisons)]
#[allow(clippy::nonminimal_bool)]
#[allow(unused_comparisons)]
fn test_unsigned_zero_comparison() {
    common::with_clean_verification(|| {
        // Declare the variable to the verification context
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        let n: u64 = 0;

        // Edge case: unsigned zero comparisons - these are intentionally tautological
        // to test that the encoder handles them correctly
        #[allow(unused_comparisons)]
        {
            assert_by!(n >= 0); // Always true for unsigned
        }
        #[allow(clippy::nonminimal_bool, unused_comparisons)]
        {
            assert_by!(!(n < 0)); // Always true for unsigned
        }

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Unsigned BV comparison now correctly uses bvuge (#2274).
        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned zero comparison should verify with correct bvuge encoding, got {:?}",
            result
        );
    })
}
