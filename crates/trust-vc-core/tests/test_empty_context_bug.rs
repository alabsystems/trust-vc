//! Test for issue #750 - empty verification context returning Verified
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

use trust_vc_core::verify_macro::verify_collected;
use trust_vc_core::VerifyResult;

/// Test that verify_collected with no context returns an error, not Verified
#[test]
fn test_empty_context_should_not_verify() {
    common::with_clean_verification(|| {
        // Call verify_collected without collecting any obligations
        let result = verify_collected();

        // This should NOT return Verified - it should be an error or Unknown
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Empty verification context should not return Verified, got: {:?}",
            result
        );

        // It should be either an Error or Unknown
        assert!(
            matches!(
                result,
                VerifyResult::Error { .. } | VerifyResult::Unknown { .. }
            ),
            "Empty context should return Error or Unknown, got: {:?}",
            result
        );
    })
}

/// Test that context with only assumptions (no assertions) returns Error.
/// Assumptions-only context returns Error — nothing to prove (#1859).
/// Previously returned Verified (vacuous truth), but this masks missing
/// postconditions. See #1859 for rationale.
#[test]
fn test_context_with_only_assumptions_returns_error() {
    use trust_vc_core::vc::ObligationKind;
    use trust_vc_core::verify_macro::{collect_obligation, collect_variable};

    common::with_clean_verification(|| {
        // Declare variable so expression resolves (typed pipeline requires this)
        collect_variable("x".to_string(), "i32".to_string());

        // Add only an assumption, no assertions
        collect_obligation(
            ObligationKind::Assume,
            "test_assumption".to_string(),
            "x > 0".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        // Assumptions-only context is an error — nothing to prove (#1859).
        match result {
            VerifyResult::Error { message } => {
                assert!(
                    message.contains("only assumptions and no assertions"),
                    "Expected assumptions-only error message (#1859), got: {}",
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
