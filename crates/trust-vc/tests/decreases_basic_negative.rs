// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for decreases/termination verification.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid termination measures
//!
//! These tests verify that invalid termination measures are properly rejected.
//! All conditions are concrete false (no free variables) — the solver must
//! always produce Counterexample. Accepting Unknown masks regressions (#1697).

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_invalid_decreases_fails_verification() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "u64".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "invalid_infinite_loop".to_string(),
            "5 + 1 < 5".to_string(),
            Some("decreases_basic_negative.rs:24".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        match result {
            VerifyResult::Counterexample { .. } => {
                // Concrete false: "5 + 1 < 5" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false '5+1 < 5' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}

#[test]
fn test_non_decreasing_recursion_fails() {
    common::with_clean_verification(|| {
        // Initialize session context so typed lowering path is available
        // (MeasureDecreases requires typed path, not legacy string translation)
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "u64".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "non_decreasing_recursion".to_string(),
            "10 < 10".to_string(),
            Some("decreases_basic_negative.rs:45".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        match result {
            VerifyResult::Counterexample { .. } => {
                // Concrete false: "10 < 10" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false '10 < 10' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}

#[test]
fn test_increasing_measure_fails() {
    common::with_clean_verification(|| {
        // Initialize session context so typed lowering path is available
        // (MeasureDecreases requires typed path, not legacy string translation)
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "u64".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "increasing_measure".to_string(),
            "(3 * 2) < 3".to_string(),
            Some("decreases_basic_negative.rs:65".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        match result {
            VerifyResult::Counterexample { .. } => {
                // Concrete false: "(3*2) < 3" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false '(3*2) < 3' must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}

#[test]
fn test_lexicographic_wrong_order_fails() {
    common::with_clean_verification(|| {
        // Initialize session context so typed lowering path is available
        // (MeasureDecreases requires typed path, not legacy string translation)
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "u64".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "bad_lexicographic".to_string(),
            "(2 < 2) || (2 == 2 && (3 + 1) < 3)".to_string(),
            Some("decreases_basic_negative.rs:93".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        match result {
            VerifyResult::Counterexample { .. } => {
                // Concrete false: "(2<2)||(2==2&&(3+1)<3)" — solver must find counterexample.
            }
            other => panic!(
                "Concrete false lexicographic must produce Counterexample, got: {:?}",
                other
            ),
        }
    })
}
