// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration test for decreases verification - ensures end-to-end correctness
//!
//! VERIFICATION LEVEL: INTEGRATION
//! Tests that the decreases macro properly verifies termination through the full pipeline

use trust_vc::decreases;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_decreases_valid_factorial() {
    common::with_clean_verification(|| {
        // Clear any previous verification context
        // Define a valid factorial function with decreases
        #[decreases(n)]
        fn factorial(n: u64) -> u64 {
            if n == 0 {
                1
            } else {
                n * factorial(n - 1)
            }
        }

        // Execute the function to trigger macro expansion
        let _ = factorial(5);

        // Collect and verify the obligations
        let pipeline = VerificationPipeline::collect_from_macros();
        let nonneg = pipeline
            .context()
            .obligations()
            .iter()
            .find(|obligation| matches!(obligation.kind(), ObligationKind::MeasureNonNegative))
            .expect("expected MeasureNonNegative obligation from #[decreases]");
        assert!(
            nonneg.condition().contains("n >= 0"),
            "expected non-negativity condition for decreases measure, got: {}",
            nonneg.condition()
        );
        assert!(
            pipeline
                .context()
                .obligations()
                .iter()
                .any(|obligation| matches!(obligation.kind(), ObligationKind::MeasureDecreases)),
            "expected MeasureDecreases obligation from recursive function"
        );
        let result = pipeline.verify();

        // Valid decreases should verify successfully
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid factorial decreases failed to verify: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_valid_fibonacci() {
    common::with_clean_verification(|| {
        #[decreases(n)]
        fn fibonacci(n: u64) -> u64 {
            if n <= 1 {
                n
            } else {
                fibonacci(n - 1) + fibonacci(n - 2)
            }
        }

        let _ = fibonacci(5);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Valid decreases with multiple recursive calls should verify
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid fibonacci decreases failed to verify: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_with_helper() {
    common::with_clean_verification(|| {
        #[decreases(n)]
        fn count_down(n: u64) -> u64 {
            if n == 0 {
                0
            } else {
                1 + count_down(n - 1)
            }
        }

        let _ = count_down(10);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid count_down decreases failed to verify: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_signed_measure_requires_non_negative_bound() {
    common::with_clean_verification(|| {
        #[decreases(n)]
        fn crosses_negative(n: i64) -> i64 {
            if n <= -1 {
                0
            } else {
                crosses_negative(n - 1)
            }
        }

        let _ = crosses_negative(0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let nonneg = pipeline
            .context()
            .obligations()
            .iter()
            .find(|obligation| matches!(obligation.kind(), ObligationKind::MeasureNonNegative))
            .expect("expected MeasureNonNegative obligation from signed #[decreases]");
        assert!(
            nonneg.condition().contains("n >= 0"),
            "expected non-negativity condition for signed measure, got: {}",
            nonneg.condition()
        );

        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Signed decreases without a non-negative precondition must not verify: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_when_skips_inactive_recursive_obligation_collection() {
    common::with_clean_verification(|| {
        #[decreases(n, when = n > 0)]
        fn partial_bad_recursion(n: i32) -> i32 {
            if n <= 0 {
                0
            } else {
                partial_bad_recursion(n + 1)
            }
        }

        let _ = partial_bad_recursion(0);
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_zero".to_string(),
            "n == 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        assert!(
            !pipeline
                .context()
                .obligations()
                .iter()
                .any(|obligation| matches!(obligation.kind(), ObligationKind::MeasureDecreases)),
            "inactive recursive branch should not collect MeasureDecreases at function entry"
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "inactive recursive branch should verify without collecting a decreases obligation: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_skips_untaken_recursive_branch_without_when() {
    common::with_clean_verification(|| {
        #[decreases(n)]
        fn partial_bad_recursion_plain(n: i32) -> i32 {
            if n <= 0 {
                0
            } else if n == 1 {
                1
            } else {
                partial_bad_recursion_plain(n + 1)
            }
        }

        let _ = partial_bad_recursion_plain(1);
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_one".to_string(),
            "n == 1".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        assert!(
            !pipeline
                .context()
                .obligations()
                .iter()
                .any(|obligation| matches!(obligation.kind(), ObligationKind::MeasureDecreases)),
            "untaken recursive branch should not collect MeasureDecreases at function entry"
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "untaken recursive branch should verify without collecting a decreases obligation: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_detects_invalid() {
    common::with_clean_verification(|| {
        // This test verifies that invalid decreases are properly rejected
        // We create the obligations manually since the macro can't express invalid decreases

        // Manually inject an invalid decreases obligation
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "u64".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "invalid_increase".to_string(),
            "(n + 1) < n".to_string(), // This is always false for u64
            Some("test_decreases_integration.rs:104".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Invalid decreases should NOT verify
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Invalid increasing measure should not verify!"
        );
    })
}
