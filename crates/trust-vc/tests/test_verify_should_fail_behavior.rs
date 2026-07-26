// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Demonstrates the bug in verify_should_fail() (issue #355).
//!
//! The problem: verify_should_fail() accepts runtime panics as "verification failures"
//! which allows tests to pass for the wrong reasons.

use trust_vc::{proof, requires};

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

#[proof]
fn false_requires_causes_runtime_panic() {
    // This will panic at runtime with "trust_vc precondition failed"
    // because requires! includes an assert! statement
    requires!(5 > 10); // FALSE - causes runtime panic
    trust_vc::assert!(true);
}

#[proof]
fn false_assertion_causes_verification_failure() {
    // This should cause a verification failure (not a runtime panic)
    trust_vc::assert!(5 > 10); // FALSE - should be caught by verifier
}

mod common;

#[test]
#[should_panic(expected = "Assumptions are contradictory")]
fn test_false_requires_panics_at_runtime() {
    common::with_clean_verification(|| {
        // requires!(5 > 10) is ghost code in test mode — it collects obligations,
        // not runtime assertions. The #[proof] auto-verify detects the contradictory
        // assumption and panics with "Assumptions are contradictory".
        false_requires_causes_runtime_panic();
    })
}

#[test]
#[allow(deprecated)]
fn test_bug_verify_should_fail_accepts_runtime_panics() {
    common::with_clean_verification(|| {
        // FIXED: This test now correctly shows that verify_should_fail
        // properly distinguishes runtime panics from verification failures
        // The proof function will panic when executed, but we need to collect
        // its obligations without executing it. However, the current architecture
        // executes proof functions at runtime in test mode.
        // We need to catch the panic to continue with the test.
        let _ = std::panic::catch_unwind(|| {
            false_requires_causes_runtime_panic();
        });

        // FIXED: Now correctly returns Err for runtime panics (issue #408)
        // Since the function panicked, no obligations were collected
        let result = expect_counterexample();

        // The bug has been fixed - verify_should_fail now properly rejects cases
        // where no verification failure occurred
        assert!(
            result.is_err(),
            "verify_should_fail should reject when no counterexample found, but got: {:?}",
            result
        );

        // Verify the error message indicates it's not a genuine counterexample.
        // After the proof fn's auto-verify panic is caught, the ContextGuard
        // restores empty state — expect_counterexample() gets "Cannot verify
        // empty context: no obligations to check" (not a real Counterexample).
        let err = result.unwrap_err();
        assert!(
            err.contains("Non-verification error")
                || err.contains("No assertions collected")
                || err.contains("no obligations")
                || err.contains("empty context"),
            "Expected non-counterexample error, got: {}",
            err
        );
    })
}

// test_deprecated_function_warning removed - deprecated helpers no longer used (#966)

#[test]
fn test_proper_verification_failure() {
    common::with_clean_verification(|| {
        // This demonstrates what a REAL verification failure should look like
        // The #[proof] macro auto-verifies and panics on failure, so we need to catch it
        let result = std::panic::catch_unwind(|| {
            false_assertion_causes_verification_failure();
        });

        // The proof function should panic with a verification failure
        assert!(
            result.is_err(),
            "Proof function should panic on verification failure"
        );

        if let Err(panic) = result {
            let msg = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();

            // Verify it's a proper verification failure, not a runtime panic
            assert!(
                msg.contains("Proof verification"),
                "Expected verification failure, got: {}",
                msg
            );
        }
    })
}

#[test]
fn test_distinguishing_failure_types() {
    common::with_clean_verification(|| {
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // DEMONSTRATION OF BUG #355
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

        // 1. Runtime Panic (from requires!):
        match std::panic::catch_unwind(false_requires_causes_runtime_panic) {
            Ok(_) => {
                // No panic - unexpected!
            }
            Err(_) => {
                // ✓ Panicked at runtime (test bug)
            }
        }

        // 2. Verification Failure (from assert!):
        let verification_failure_result = std::panic::catch_unwind(|| {
            false_assertion_causes_verification_failure();
        });
        assert!(
            verification_failure_result.is_err(),
            "Should panic with verification failure"
        );

        if let Err(panic) = verification_failure_result {
            let msg = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            assert!(
                msg.contains("Proof verification"),
                "Expected verification failure, got: {}",
                msg
            );
        }

        // Now they ARE distinguished - runtime panics vs verification failures
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    })
}

/// Regression test for #1956: verify_should_fail must NOT silently convert
/// non-verification panics (index OOB, unwrap on None, etc.) into
/// Counterexample results. Such infrastructure panics must propagate.
#[test]
#[should_panic(expected = "infrastructure bug, not a proof rejection")]
fn test_verify_should_fail_rejects_infrastructure_panics() {
    // A proof function that panics with a non-verification message
    // (simulating an infrastructure bug like index OOB or unwrap failure)
    let _ = common::verify_should_fail(|| {
        panic!("index out of bounds: the len is 3 but the index is 5");
    });
}

/// Regression test for #1956: verify_should_fail still accepts genuine
/// verification failures (from the auto-verify mechanism).
#[test]
fn test_verify_should_fail_accepts_verification_failures() {
    let result = common::verify_should_fail(|| {
        false_assertion_causes_verification_failure();
    });
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Counterexample { .. }
                | trust_vc_core::VerifyResult::Unknown { .. }
        ),
        "Expected proof rejection from genuine verification failure, got: {:?}",
        result
    );
}

/// Regression test: verify_should_fail must treat solver Unknown as a genuine
/// proof rejection, not as an infrastructure panic.
#[test]
fn test_verify_should_fail_accepts_unknown_rejections() {
    let result = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn contradictory_proof() {
            let x = 4;
            trust_vc::assume!(x > 5);
            trust_vc::assume!(x < 3);
            trust_vc::assert!(x == 4);
        }

        contradictory_proof();
    });
    assert!(
        matches!(result, trust_vc_core::VerifyResult::Unknown { .. }),
        "Expected Unknown from contradictory assumptions, got: {:?}",
        result
    );
}

/// Regression test for #1713: verify_should_pass must detect closures that
/// collect zero obligations (silent vacuous pass).
#[test]
#[should_panic(expected = "zero obligations")]
fn test_verify_should_pass_rejects_vacuous_pass() {
    let _ = common::verify_should_pass(|| {
        // Empty closure — no proof function, no assertions, no obligations.
        // Previously returned Verified silently; now must panic.
    });
}

/// Regression test for #1713: verify_and_get_result returns Error for
/// zero-obligation closures instead of silently returning Verified.
#[test]
fn test_verify_and_get_result_returns_error_for_vacuous_pass() {
    let result = common::verify_and_get_result(|| {
        // Empty closure — no obligations collected.
    });
    assert!(
        matches!(result, trust_vc_core::VerifyResult::Error { .. }),
        "Expected Error for vacuous pass, got: {:?}",
        result
    );
}

/// Positive regression: verify_should_pass still works for real proofs.
#[test]
fn test_verify_should_pass_accepts_real_proof() {
    let result = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn trivial_proof() {
            trust_vc::assert!(true);
        }
        trivial_proof();
    });
    assert!(
        matches!(result, trust_vc_core::VerifyResult::Verified),
        "Expected Verified for real proof, got: {:?}",
        result
    );
}
