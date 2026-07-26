// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// loop_decreases! tests
// ============================================================================
#[test]
fn test_loop_decreases_compiles() {
    common::with_clean_verification(|| {
        // Declare variable to the verification context
        verify_macro::collect_variable("n".to_string(), "i64".to_string());

        // Model the inductive step: loop guard holds and body decrements n.
        // n represents the post-body value; n_entry is the pre-body value.
        // The body does n -= 1, so n_entry == n + 1.
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "n >= 0".to_string(),
            None,
        );

        // Basic decreases measure
        let mut n: i64 = 10;
        while n > 0 {
            loop_decreases!(n);
            n -= 1;
        }

        // Add body model: entry value was one more than current (body did n -= 1)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_decrement".to_string(),
            "n_entry == n + 1".to_string(),
            None,
        );

        // Verify decreases measure was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Basic decreases measure should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_expression() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        // Measure: n - i; sanitized entry var: n_minus_i_entry
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Model the inductive step for measure (n - i):
        // Variables are non-negative and loop guard holds
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_nonneg".to_string(),
            "i >= 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_nonneg".to_string(),
            "n >= 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "i < n".to_string(),
            None,
        );

        // Decreases with expression
        let mut i = 0;
        let n = 10;
        while i < n {
            loop_decreases!(n - i);
            i += 1;
        }

        // Body model: body does i += 1, so measure (n-i) decreased by 1.
        // Entry measure was one more than current: n_minus_i_entry == (n - i) + 1
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_effect".to_string(),
            "n_minus_i_entry == n - i + 1".to_string(),
            None,
        );

        // Verify expression decreases measure was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Expression decreases measure should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_unsigned() {
    common::with_clean_verification(|| {
        // Declare variable to the verification context
        verify_macro::collect_variable("n".to_string(), "u64".to_string());

        // Model the inductive step: loop guard + body decrement
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "n >= 0".to_string(),
            None,
        );

        // Works with unsigned types
        let mut n: u64 = 10;
        while n > 0 {
            loop_decreases!(n);
            n -= 1;
        }

        // Body model: body does n -= 1, so entry was one more
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_decrement".to_string(),
            "n_entry == n + 1".to_string(),
            None,
        );

        // Verify unsigned decreases measure was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Unsigned decreases measure should verify"
            ),
        }
    })
}
