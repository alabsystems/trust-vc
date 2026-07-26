// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for obligation kind soundness
//!
//! These tests verify that each ObligationKind correctly accepts/rejects conditions.
//! Assert and Ensures are checked as assertions (must hold).
//! Requires and Assume are assumptions (trusted, not checked).
//!
//! Issue #1399: Requires semantics clarified - it IS an assumption (precondition)

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

/// Clear all thread-local verification state (matches common::with_clean_verification internals)
fn clear_all_state() {
    verify_macro::clear_all_thread_locals();
    trust_vc_core::verification_bridge::clear_registrations();
    trust_vc_core::clear_extern_contracts();
}

/// Test that an obligation kind correctly rejects false
fn test_rejects_false(kind: ObligationKind, kind_name: &str) {
    clear_all_state();

    verify_macro::collect_obligation(
        kind,
        format!("{}_false", kind_name),
        "false".to_string(),
        Some(format!("soundness_test:{}", kind_name)),
    );

    let pipeline = VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "SOUNDNESS BUG: {} accepted 'false' as true! Got: {:?}",
        kind_name,
        result
    );
}

/// Test that an obligation kind correctly accepts true
fn test_accepts_true(kind: ObligationKind, kind_name: &str) {
    clear_all_state();

    verify_macro::collect_obligation(
        kind,
        format!("{}_true", kind_name),
        "true".to_string(),
        Some(format!("soundness_test:{}", kind_name)),
    );

    let pipeline = VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "{} should accept 'true', got: {:?}",
        kind_name,
        result
    );
}

mod common;

#[test]
fn test_assert_soundness() {
    common::with_clean_verification(|| {
        test_rejects_false(ObligationKind::Assert, "Assert");
        test_accepts_true(ObligationKind::Assert, "Assert");
    })
}

#[test]
fn test_requires_soundness() {
    common::with_clean_verification(|| {
        // Requires is a precondition (assumption), NOT an assertion.
        // After #2233 fail-closed fix, assumption-only contexts (no assertions)
        // return Error because there's nothing to prove. This is correct:
        // the pipeline refuses to report Verified when no assertion was checked.

        // Requires("false") alone = no assertions = Error (fail-closed, #2233)
        clear_all_state();
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            Some("soundness_test:requires".to_string()),
        );
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Requires('false') with no assertions should be Error (nothing to prove), got: {:?}",
            result
        );

        // Requires("false") + Assert("true") = vacuous truth detected (#2258)
        // The pipeline detects contradictory assumptions and returns Unknown
        clear_all_state();
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false_2".to_string(),
            "false".to_string(),
            Some("soundness_test:requires".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_true".to_string(),
            "true".to_string(),
            Some("soundness_test:requires".to_string()),
        );
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Requires('false') + Assert('true') should be Unknown (vacuous truth #2258), got: {:?}",
            result
        );

        // Requires("true") + Assert("true") = Verified
        clear_all_state();
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_true".to_string(),
            "true".to_string(),
            Some("soundness_test:requires".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_true_2".to_string(),
            "true".to_string(),
            Some("soundness_test:requires".to_string()),
        );
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Requires('true') + Assert('true') should be Verified, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_soundness() {
    common::with_clean_verification(|| {
        test_rejects_false(ObligationKind::Ensures, "Ensures");
        test_accepts_true(ObligationKind::Ensures, "Ensures");
    })
}

#[test]
fn test_assume_behavior() {
    common::with_clean_verification(|| {
        // After #2233 fail-closed fix, assumption-only contexts return Error
        // because there's nothing to prove.
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_false".to_string(),
            "false".to_string(),
            Some("soundness_test:assume".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Assume(false) with no assertions should be Error (nothing to prove, #2233), got: {:?}",
            result
        );

        // Assume(false) + Assert(true) = vacuous truth detected (#2258)
        // The pipeline detects contradictory assumptions and returns Unknown
        clear_all_state();
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_false_2".to_string(),
            "false".to_string(),
            Some("soundness_test:assume".to_string()),
        );
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_true_under_assume".to_string(),
            "true".to_string(),
            Some("soundness_test:assume".to_string()),
        );
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Assume(false) + Assert(true) should be Unknown (vacuous truth #2258), got: {:?}",
            result
        );
    })
}

#[test]
fn test_complex_false_expressions() {
    common::with_clean_verification(|| {
        // Test that various false expressions are rejected by assertion kinds.
        // Only Assert and Ensures are checked as assertions.
        // Requires is an assumption - see test_requires_soundness for its semantics.
        let false_exprs = vec![
            ("0 > 0", "zero_gt_zero"),
            ("1 == 2", "one_eq_two"),
            ("5 < 3", "five_lt_three"),
            ("true && false", "true_and_false"),
            ("!true", "not_true"),
        ];

        for (expr, name) in false_exprs {
            for kind in [ObligationKind::Assert, ObligationKind::Ensures] {
                clear_all_state();

                verify_macro::collect_obligation(
                    kind,
                    format!("{}_{:?}", name, kind),
                    expr.to_string(),
                    Some("soundness_test:complex".to_string()),
                );

                let pipeline = VerificationPipeline::collect_from_macros();
                let result = pipeline.verify();

                assert!(
                    matches!(result, VerifyResult::Counterexample { .. }),
                    "SOUNDNESS BUG: {:?} accepted '{}' as true! Got: {:?}",
                    kind,
                    expr,
                    result
                );
            }
        }
    })
}

#[test]
fn test_complex_true_expressions() {
    common::with_clean_verification(|| {
        // Test that various true expressions are accepted
        let true_exprs = vec![
            ("1 > 0", "one_gt_zero"),
            ("2 == 2", "two_eq_two"),
            ("3 < 5", "three_lt_five"),
            ("true || false", "true_or_false"),
            ("!false", "not_false"),
        ];

        for (expr, name) in true_exprs {
            // Only Assert and Ensures are checked as assertions.
            // Requires is an assumption - see test_requires_soundness for its semantics.
            for kind in [ObligationKind::Assert, ObligationKind::Ensures] {
                clear_all_state();

                verify_macro::collect_obligation(
                    kind,
                    format!("{}_{:?}", name, kind),
                    expr.to_string(),
                    Some("soundness_test:complex".to_string()),
                );

                let pipeline = VerificationPipeline::collect_from_macros();
                let result = pipeline.verify();

                assert!(
                    matches!(result, VerifyResult::Verified),
                    "{:?} should accept '{}', got: {:?}",
                    kind,
                    expr,
                    result
                );
            }
        }
    })
}
