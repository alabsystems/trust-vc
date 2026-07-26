//! Test for issue #365 - verify_collected bug
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, verify_collected};
use trust_vc_core::VerifyResult;

#[test]
fn test_verify_collected_with_false() {
    common::with_clean_verification(|| {
        // Collect a false obligation
        collect_obligation(
            ObligationKind::Assert,
            "false_claim".to_string(),
            "false".to_string(),
            Some("test:19:1".to_string()),
        );

        // Verify what was collected
        let result = verify_collected();

        // It should NOT verify!
        match result {
            VerifyResult::Verified => {
                panic!("BUG: verify_collected returned Verified for 'false'!");
            }
            VerifyResult::Counterexample { .. } => {
                // Expected: false assertion produces counterexample
            }
            _ => {
                panic!("Unexpected result: {:?}", result);
            }
        }
    })
}

#[test]
fn test_verify_collected_empty_context() {
    common::with_clean_verification(|| {
        // Verify empty context
        let result = verify_collected();

        // Empty context should return an Error because no context was initialized
        // This verifies that issue #808 is fixed
        match result {
            VerifyResult::Error { message } => {
                assert!(message.contains("No verification context initialized"));
            }
            VerifyResult::Verified => {
                panic!("BUG: Empty context returns Verified (should be Error)");
            }
            _ => {
                panic!("Unexpected result for empty context: {:?}", result);
            }
        }
    })
}

#[test]
fn test_clear_context_then_verify() {
    common::with_clean_verification(|| {
        // Add an obligation
        collect_obligation(
            ObligationKind::Assert,
            "test1".to_string(),
            "true".to_string(),
            None,
        );

        // Clear all state to re-enter clean state (full cleanup including
        // registrations and extern contracts, not just verify_macro context)
        trust_vc_core::verify_macro::clear_all_thread_locals();
        trust_vc_core::verification_bridge::clear_registrations();
        trust_vc_core::clear_extern_contracts();

        // Now collect a false one
        collect_obligation(
            ObligationKind::Assert,
            "test2".to_string(),
            "false".to_string(),
            None,
        );

        // Verify
        let result = verify_collected();

        // Should get counterexample
        assert!(matches!(result, VerifyResult::Counterexample { .. }));
    })
}
