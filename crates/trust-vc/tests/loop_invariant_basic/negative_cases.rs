// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// Negative tests - invalid invariants should be rejected
// ============================================================================
/// Non-tautological invariant correctly rejected by inductive step (#1609).
///
/// With the inductive step now implemented, `i >= 0` (signed i32) is correctly
/// rejected — it's not universally valid over all i32 values.
#[test]
fn test_invalid_invariant_rejected() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("i".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        let mut i = 0;
        while i < 10 {
            invariant!(i >= 0);
            i += 1;
        }

        // Inductive step correctly rejects: i >= 0 not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

#[test]
fn test_non_decreasing_loop_rejected() {
    common::with_clean_verification(|| {
        // Test a non-decreasing loop measure.
        // With decrease checking (#825), the verifier now checks that the
        // measure strictly decreases (i < i_entry). Since i increases in
        // this loop, the decrease check correctly produces a counterexample.
        verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Add assumption about initial value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        let mut i = 0;
        while i < 10 {
            // This measure doesn't decrease - it increases!
            loop_decreases!(i);
            i += 1;
        }

        // Decrease checking: i < i_entry fails when i_entry = 0 (counterexample)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-decreasing loop measure should be rejected by decrease check, got: {:?}",
            result
        );
    })
}
