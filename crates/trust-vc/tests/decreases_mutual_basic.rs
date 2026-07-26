// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for mutual recursion termination proofs via `#[decreases(m, mutual_with(...))]`.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline.

use trust_vc::decreases;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

// -- Mutual recursion pair: is_even / is_odd --

#[decreases(n, mutual_with(is_odd))]
fn is_even(n: u64) -> bool {
    if n == 0 {
        true
    } else {
        is_odd(n - 1)
    }
}

#[decreases(n, mutual_with(is_even))]
fn is_odd(n: u64) -> bool {
    if n == 0 {
        false
    } else {
        is_even(n - 1)
    }
}

#[test]
fn test_mutual_recursion_compiles_and_executes() {
    common::with_clean_verification(|| {
        assert!(is_even(0));
        assert!(!is_odd(0));
        assert!(!is_even(1));
        assert!(is_odd(1));
        assert!(is_even(4));
        assert!(is_odd(5));
        assert!(!is_even(7));
        assert!(!is_odd(8));
    })
}

#[test]
fn test_mutual_recursion_collects_decrease_obligations() {
    common::with_clean_verification(|| {
        // Call is_even to trigger obligation collection in test mode
        let _ = is_even(3);

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        // Should have MeasureDecreases obligations for the mutual call is_odd(n-1)
        let decrease_obligations: Vec<_> = obligations
            .iter()
            .filter(|o| o.kind() == ObligationKind::MeasureDecreases)
            .collect();

        assert!(
            !decrease_obligations.is_empty(),
            "mutual recursion should generate MeasureDecreases obligations, got: {:?}",
            obligations
                .iter()
                .map(|o| (o.name(), o.kind()))
                .collect::<Vec<_>>()
        );
    })
}

#[test]
fn test_mutual_decreases_valid_verifies() {
    common::with_clean_verification(|| {
        // Simulate is_even(5) calling is_odd(4): measure 4 < 5
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::MeasureDecreases,
            "is_even:mutual_call_0".to_string(),
            "(n - 1u64) < n".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "valid mutual decreases should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_mutual_decreases_invalid_fails() {
    common::with_clean_verification(|| {
        // Simulate a broken mutual recursion where measure doesn't decrease
        // e.g., is_even(n) calls is_odd(n+1) — measure goes UP
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::MeasureDecreases,
            "is_even:bad_mutual_call".to_string(),
            "(n + 1u64) < n".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "invalid mutual decreases should NOT verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_mutual_decreases_same_value_fails() {
    common::with_clean_verification(|| {
        // Simulate mutual call with same measure (infinite loop)
        // e.g., is_even(n) calls is_odd(n) — no decrease
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_value".to_string(),
            "n == 3u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            ObligationKind::MeasureDecreases,
            "is_even:mutual_no_decrease".to_string(),
            "n < n".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "mutual call with same measure should NOT verify, got: {:?}",
            result
        );
    })
}
