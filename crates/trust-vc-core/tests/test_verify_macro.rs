//! Tests for verify_macro module
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

#[test]
fn test_verify_simple_proof() {
    common::with_clean_verification(|| {
        // Test that a symbolic ensures condition verifies when implied by assumption
        collect_variable("x".to_string(), "u64".to_string());

        collect_obligation(
            ObligationKind::Assume,
            "x_positive".to_string(),
            "x > 0".to_string(),
            Some("test:14:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Ensures,
            "x_nonneg".to_string(),
            "x >= 1".to_string(),
            Some("test:14:2".to_string()),
        );

        let result = verify_collected();

        // x > 0 implies x >= 1, ay must reason about this
        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 should imply x >= 1, got: {:?}",
            result
        );
    });
}

#[test]
fn test_verify_with_assumption() {
    // Test that a requires assumption enables proving a weaker ensures
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        // Requires: x > 5
        collect_obligation(
            ObligationKind::Requires,
            "x_gt_five".to_string(),
            "x > 5".to_string(),
            Some("test:41:1".to_string()),
        );

        // Ensures: x > 4 (follows from x > 5)
        collect_obligation(
            ObligationKind::Ensures,
            "x_gt_four".to_string(),
            "x > 4".to_string(),
            Some("test:49:1".to_string()),
        );

        let result = verify_collected();

        // x > 5 implies x > 4, ay must reason symbolically
        assert!(
            matches!(result, VerifyResult::Verified),
            "Proof with assumption x > 5 ⊢ x > 4 should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_false_ensures_fails() {
    // Test that a false ensures condition is rejected with counterexample
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 0 (satisfiable)
        collect_obligation(
            ObligationKind::Assume,
            "x_positive".to_string(),
            "x > 0".to_string(),
            Some("test:72:1".to_string()),
        );

        // Ensures: x < 0 (contradicts assumption — must fail)
        collect_obligation(
            ObligationKind::Ensures,
            "false_ensures".to_string(),
            "x < 0".to_string(),
            Some("test:72:2".to_string()),
        );

        let result = verify_collected();

        // ay should find counterexample: any x > 0 violates x < 0
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Ensures x < 0 with assume x > 0 should return counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_contradictory_assumptions() {
    // Contradictory requires clauses are detected by vacuous truth check (#2258).
    // When assumptions are UNSAT, the verifier returns Unknown instead of
    // silently reporting Verified — prevents false confidence from ex falso.
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        // Contradictory symbolic requires: x > 10 AND x < 3
        collect_obligation(
            ObligationKind::Requires,
            "x_gt_ten".to_string(),
            "x > 10".to_string(),
            Some("test:94:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Requires,
            "x_lt_three".to_string(),
            "x < 3".to_string(),
            Some("test:101:1".to_string()),
        );

        // Absurd assertion that only holds under contradiction
        collect_obligation(
            ObligationKind::Assert,
            "absurd".to_string(),
            "x > 1000000".to_string(),
            Some("test:108:1".to_string()),
        );

        let result = verify_collected();

        // Vacuous truth detection (#2258): contradictory assumptions return
        // Unknown with explanation, not Verified.
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("contradictory")),
            "Contradictory requires should be detected as vacuous truth, got: {:?}",
            result
        );
    })
}

/// Malformed expressions panic at collection time per #1723 invariant.
/// Expressions come from stringify!() and are always valid Rust syntax.
#[test]
fn test_invalid_syntax_panics() {
    trust_vc_core::verify_macro::clear_all_thread_locals();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        collect_obligation(
            ObligationKind::Assert,
            "malformed".to_string(),
            "(5 + 1 > 3".to_string(), // Missing closing paren — invalid Rust syntax
            Some("test:131:1".to_string()),
        );
    }));

    trust_vc_core::verify_macro::clear_all_thread_locals();

    assert!(
        result.is_err(),
        "Malformed expression should panic per #1723"
    );
    let err = result.unwrap_err();
    let msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .unwrap_or("");
    assert!(
        msg.contains("#1723"),
        "Panic should reference #1723, got: {}",
        msg
    );
}

#[test]
fn test_complex_arithmetic_symbolic() {
    // Test that complex symbolic arithmetic verifies through ay
    common::with_clean_verification(|| {
        collect_variable("a".to_string(), "u32".to_string());
        collect_variable("b".to_string(), "u32".to_string());

        // Bound values to prevent overflow
        collect_obligation(
            ObligationKind::Assume,
            "a_bound".to_string(),
            "a > 0 && a <= 1000".to_string(),
            Some("test:159:1".to_string()),
        );
        collect_obligation(
            ObligationKind::Assume,
            "b_bound".to_string(),
            "b > 0 && b <= 1000".to_string(),
            Some("test:159:2".to_string()),
        );

        // Complex property: a * b > 0 when both positive
        collect_obligation(
            ObligationKind::Ensures,
            "product_positive".to_string(),
            "a * b > 0".to_string(),
            Some("test:159:3".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Product of bounded positive u32s should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_empty_context_returns_error() {
    // Test that an empty context returns Error (soundness bug #808 fix)
    common::with_clean_verification(|| {
        let result = verify_collected();

        // Empty context should return Error after fix for soundness bug #808
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Empty context should return Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_assumptions_only_context_returns_error() {
    // Soundness regression (#1859): assumptions-only contexts are an API error,
    // not vacuously verified proofs.
    common::with_clean_verification(|| {
        // Declare variable so expression resolves (typed pipeline requires this)
        collect_variable("x".to_string(), "i32".to_string());

        collect_obligation(
            ObligationKind::Requires,
            "requires_only".to_string(),
            "x > 0".to_string(),
            Some("test:205:1".to_string()),
        );

        let result = verify_collected();
        match result {
            VerifyResult::Error { message } => {
                assert!(
                    message.contains("only assumptions and no assertions"),
                    "Assumptions-only context must return Error (#1859), got: {}",
                    message
                );
            }
            _ => panic!(
                "Assumptions-only context should return Error (#1859), got: {:?}",
                result
            ),
        }
    })
}
