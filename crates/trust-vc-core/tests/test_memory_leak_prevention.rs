//! Test that verifies thread-local storage doesn't leak memory
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{
    clear_all_thread_locals, collect_obligation, get_context, verify_collected,
};
use trust_vc_core::VerifyResult;

#[test]
fn test_no_thread_local_leak() {
    common::with_clean_verification(|| {
        // Verify that clear_all_thread_locals() actually resets context to None
        // and that obligations from one iteration don't accumulate into the next.

        for i in 0..10 {
            collect_obligation(
                ObligationKind::Ensures,
                format!("test_ensures_{}", i),
                format!("x_{} > 0", i),
                Some(format!("test:{}:1", i)),
            );

            collect_obligation(
                ObligationKind::Assert,
                format!("test_assert_{}", i),
                "true".to_string(),
                Some(format!("test:{}:1", i)),
            );

            // Context should have exactly 2 obligations from this iteration
            let ctx = get_context().expect("context should exist after collect");
            assert_eq!(
                ctx.obligations().len(),
                2,
                "iteration {}: expected 2 obligations, got {} (state leaked from prior iteration)",
                i,
                ctx.obligations().len()
            );

            let _result = verify_collected();

            clear_all_thread_locals();

            // After cleanup, context must be None — not an empty context
            assert!(
                get_context().is_none(),
                "iteration {}: context should be None after clear_all_thread_locals()",
                i
            );
        }
    });
}

#[test]
fn test_cleanup_after_verification_error() {
    common::with_clean_verification(|| {
        // Start clean
        clear_all_thread_locals();

        // Create an obligation that will fail
        collect_obligation(
            ObligationKind::Assert,
            "will_fail".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        // Verify it (should get counterexample)
        let result = verify_collected();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Should get counterexample for false assertion"
        );

        // Clear after error
        clear_all_thread_locals();

        // Verify cleanup worked
        // Verify cleanup worked by trying another verification
        collect_obligation(
            ObligationKind::Assert,
            "after_cleanup".to_string(),
            "true".to_string(),
            Some("test:2:1".to_string()),
        );
        let result2 = verify_collected();
        assert!(matches!(result2, VerifyResult::Verified));
    });
}

#[test]
fn test_cleanup_between_test_runs() {
    // First test run — collects an obligation named "first_test"
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Ensures,
            "first_test".to_string(),
            "x > 10".to_string(),
            Some("test:1:1".to_string()),
        );
        let ctx = get_context().expect("context should exist after first collect");
        assert_eq!(ctx.obligations().len(), 1);
        assert_eq!(ctx.obligations()[0].name(), "first_test");
        let _result = verify_collected();
    });

    // After with_clean_verification, context must be cleared
    assert!(
        get_context().is_none(),
        "context should be None after with_clean_verification cleanup"
    );

    // Second test run — should NOT see "first_test" obligation
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Assert,
            "second_test".to_string(),
            "y < 5".to_string(),
            Some("test:2:1".to_string()),
        );

        let ctx = get_context().expect("context should exist after second collect");
        assert_eq!(
            ctx.obligations().len(),
            1,
            "second run should have exactly 1 obligation, not {} (first run leaked)",
            ctx.obligations().len()
        );
        assert_eq!(ctx.obligations()[0].name(), "second_test");
        // Verify the first run's obligation is NOT present
        assert!(
            !ctx.obligations().iter().any(|o| o.name() == "first_test"),
            "first_test obligation leaked into second test run"
        );
        let _result = verify_collected();
    });
}

#[test]
fn test_repeated_verification_with_cleanup() {
    common::with_clean_verification(|| {
        for round in 0..10 {
            clear_all_thread_locals();

            // After cleanup, context must be gone
            assert!(
                get_context().is_none(),
                "round {}: context should be None after clear",
                round
            );

            for i in 0..5 {
                collect_obligation(
                    ObligationKind::Assert,
                    format!("round_{}_assert_{}", round, i),
                    "true".to_string(),
                    Some(format!("test:{}:{}:1", round, i)),
                );
            }

            // Verify exactly 5 obligations — no accumulation from prior rounds
            let ctx = get_context().expect("context should exist after 5 collects");
            assert_eq!(
                ctx.obligations().len(),
                5,
                "round {}: expected 5 obligations, got {} (state accumulated from prior round)",
                round,
                ctx.obligations().len()
            );
            // Verify obligation names belong to THIS round only
            for ob in ctx.obligations() {
                assert!(
                    ob.name().starts_with(&format!("round_{}_", round)),
                    "round {}: found obligation '{}' from a different round",
                    round,
                    ob.name()
                );
            }

            let result = verify_collected();
            assert!(matches!(result, VerifyResult::Verified));
        }
    });
}
