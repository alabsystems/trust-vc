//! Test that verifies the correct semantics of ObligationKind::Requires
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This test verifies that Requires obligations are correctly treated
//! as assumptions in function body verification (not assertions).
//! Assumptions-only contexts return Error (#1859).

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

/// requires(false) alone returns Error — nothing to prove (#1859).
#[test]
fn test_requires_false_returns_error() {
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Requires('false') alone should return Error (#1859), got: {:?}",
            result
        );
    });
}

/// Symbolic requires-only context returns Error — nothing to prove (#1859).
/// This tests the typed pipeline path with a real variable.
#[test]
fn test_requires_symbolic_returns_error() {
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());

        collect_obligation(
            ObligationKind::Requires,
            "requires_x_positive".to_string(),
            "x > 0".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        match result {
            VerifyResult::Error { message } => {
                assert!(
                    message.contains("only assumptions and no assertions"),
                    "Requires-only context must mention 'only assumptions and no assertions', got: {}",
                    message
                );
            }
            _ => panic!(
                "Requires-only with symbolic variable should return Error (#1859), got: {:?}",
                result
            ),
        }
    });
}

#[test]
fn test_assume_false_with_assert_false_is_verified() {
    common::with_clean_verification(|| {
        // This tests that Assume still works as an assumption
        // If we assume false, we can prove anything (even false)

        collect_obligation(
            ObligationKind::Assume,
            "assume_false".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        collect_obligation(
            ObligationKind::Assert,
            "assert_false".to_string(),
            "false".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        // Vacuous truth detection (#2258): assume(false) makes assumptions
        // contradictory → caught and reported as Unknown.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Assume(false) should be caught by vacuous truth check, got: {:?}",
            result
        );
    });
}
