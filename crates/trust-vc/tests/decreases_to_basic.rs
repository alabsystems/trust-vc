// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for decreases_to! macro - lexicographic decrease relation.
//!
//! Verifies that decreases_to! compiles and type-checks correctly.
//! Actual ay ordering verification happens when processed by trust_mc.
//!
//! FIXED (#758): Now verifies decreases relations, not just runtime behavior.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::decreases_to;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

mod common;

#[test]
fn test_decreases_to_compiles() {
    common::with_clean_verification(|| {
        // Basic single-element decrease
        // Note: decreases_to! is a verification-time check, not runtime
        // The macro generates a marker for trust_mc to verify the relation
        let _result = decreases_to!(10i64 => 5i64);

        // This needs to be verified by the SMT solver
        // Currently we can't verify decreases relations without a proof function context
        // Proper decreases verification blocked on proof function support (#1353).
    })
}

#[test]
fn test_decreases_to_lexicographic_two() {
    common::with_clean_verification(|| {
        // Two-element lexicographic decrease (first stays, second decreases)
        let result = decreases_to!(5i64, 10i64 => 5i64, 3i64);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_lexicographic_first_decreases() {
    common::with_clean_verification(|| {
        // First element decreases (second doesn't matter)
        let result = decreases_to!(10i64, 1i64 => 5i64, 100i64);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_lexicographic_three() {
    common::with_clean_verification(|| {
        // Three-element lexicographic
        let result = decreases_to!(5i64, 5i64, 10i64 => 5i64, 5i64, 3i64);
        assert!(result);
    })
}

#[test]
#[allow(unused_variables)]
fn test_decreases_to_with_variables() {
    common::with_clean_verification(|| {
        // Variables in decreases_to! - used in macro expansion but compiler can't see it
        let m = 10i64;
        let n = 5i64;
        let m_prime = 10i64;
        let n_prime = 3i64;
        let result = decreases_to!(m, n => m_prime, n_prime);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_ackermann_case1() {
    common::with_clean_verification(|| {
        // Ackermann: ackermann(m-1, 1) when m > 0, n == 0
        // (m, n) = (3, 0) => (2, 1)
        // m decreases: 3 > 2
        let result = decreases_to!(3i64, 0i64 => 2i64, 1i64);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_ackermann_case2() {
    common::with_clean_verification(|| {
        // Ackermann: ackermann(m, n-1) when m > 0, n > 0
        // (m, n) = (2, 5) => (2, 4)
        // m stays, n decreases: 5 > 4
        let result = decreases_to!(2i64, 5i64 => 2i64, 4i64);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_ackermann_case3() {
    common::with_clean_verification(|| {
        // Ackermann: ackermann(m-1, inner) for outer call
        // (m, n) = (3, 2) => (2, something)
        // m decreases: 3 > 2
        let result = decreases_to!(3i64, 2i64 => 2i64, 999i64);
        assert!(result);
    })
}

#[test]
fn test_decreases_to_u64() {
    common::with_clean_verification(|| {
        // Works with u64 types
        let result = decreases_to!(100u64 => 50u64);
        assert!(result);
    })
}

#[test]
#[allow(unused_variables)]
fn test_decreases_to_mixed_expressions() {
    common::with_clean_verification(|| {
        // Expressions in decreases_to! - x used in macro expansion
        let x = 10i64;
        let result = decreases_to!(x * 2 => x);
        assert!(result);
    })
}

// ========================================================================
// Negative tests: non-decreasing cases must return false (#1548)
// Before the fix, decreases_to! always returned true regardless of values.
// ========================================================================

#[test]
fn test_decreases_to_increase_is_false() {
    common::with_clean_verification(|| {
        // An increase (1 => 100) must NOT be accepted as a decrease
        let result = decreases_to!(1i64 => 100i64);
        assert!(
            !result,
            "decreases_to!(1 => 100) should be false (not a decrease)"
        );
    })
}

#[test]
fn test_decreases_to_equal_is_false() {
    common::with_clean_verification(|| {
        // Equal values are not a decrease
        let result = decreases_to!(5i64 => 5i64);
        assert!(
            !result,
            "decreases_to!(5 => 5) should be false (no decrease)"
        );
    })
}

#[test]
fn test_decreases_to_lex_increase_second_is_false() {
    common::with_clean_verification(|| {
        // First equal, second increases — NOT a decrease
        let result = decreases_to!(5i64, 3i64 => 5i64, 10i64);
        assert!(
            !result,
            "decreases_to!(5, 3 => 5, 10) should be false (second increases)"
        );
    })
}

#[test]
fn test_decreases_to_first_increases_is_false() {
    common::with_clean_verification(|| {
        // First increases — NOT a decrease, even if second decreases
        let result = decreases_to!(3i64, 10i64 => 5i64, 1i64);
        assert!(
            !result,
            "decreases_to!(3, 10 => 5, 1) should be false (first increases)"
        );
    })
}

#[test]
fn test_decreases_to_verification_valid() {
    common::with_clean_verification(|| {
        // FIXED (#758): Test that valid decreases relations verify
        // Declare variables for verification
        trust_vc_core::verify_macro::collect_variable("n1".to_string(), "u64".to_string());
        trust_vc_core::verify_macro::collect_variable("n2".to_string(), "u64".to_string());

        // Add assumptions
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n1_value".to_string(),
            "n1 == 10".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n2_value".to_string(),
            "n2 == 5".to_string(),
            None,
        );

        // Assert the decrease relation
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "decreases_to".to_string(),
            "n1 > n2".to_string(), // 10 > 5 should verify
            None,
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Valid decreases relation should verify"
            ),
        }
    })
}

#[test]
fn test_decreases_to_verification_invalid() {
    common::with_clean_verification(|| {
        // FIXED (#758): Negative test - invalid decreases must fail
        trust_vc_core::verify_macro::collect_variable("n1".to_string(), "u64".to_string());
        trust_vc_core::verify_macro::collect_variable("n2".to_string(), "u64".to_string());

        // Set up values that DON'T decrease
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n1_value".to_string(),
            "n1 == 5".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n2_value".to_string(),
            "n2 == 10".to_string(),
            None,
        );

        // Assert an INVALID decrease (5 > 10 is false)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "invalid_decreases".to_string(),
            "n1 > n2".to_string(),
            None,
        );

        expect_counterexample().expect("Invalid decreases relation should produce counterexample");
    })
}
