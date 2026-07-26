// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// Combined tests
// ============================================================================
#[test]
fn test_invariant_and_decreases() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        // Measure: n - i; sanitized entry var: n_minus_i_entry
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Model the inductive step: loop guard + invariant base
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "i < n".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_nonneg".to_string(),
            "i >= 0".to_string(),
            None,
        );

        // Both invariant and decreases in same loop
        let mut i = 0;
        let n = 10;
        while i < n {
            invariant!(i >= 0 && i <= n);
            loop_decreases!(n - i);
            i += 1;
        }

        // Body model: i += 1, so measure (n-i) decreased by 1
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_effect".to_string(),
            "n_minus_i_entry == n - i + 1".to_string(),
            None,
        );

        // Inductive step rejects invariant: i >= 0 && i <= n not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

/// For loop invariant: `sum >= 0` (signed i32) fails inductive step (#1609).
#[test]
fn test_for_loop_invariant() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("sum".to_string(), "i32".to_string());
        verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Add assumption about initial value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "sum_init".to_string(),
            "sum == 0".to_string(),
            None,
        );

        // Invariant works in for loops too
        let mut sum = 0;
        for i in 0..10 {
            invariant!(sum >= 0);
            sum += i;
        }
        assert!(sum > 0);

        // Inductive step rejects: sum >= 0 not universally valid for signed i32 (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

/// Nested loop invariants: range constraints not universally valid (#1609).
#[test]
fn test_nested_loops() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("outer".to_string(), "i32".to_string());
        verify_macro::collect_variable("inner".to_string(), "i32".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_init".to_string(),
            "outer == 0".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_init".to_string(),
            "inner == 0".to_string(),
            None,
        );

        // Invariants in nested loops — use comparisons instead of Range::contains
        let mut outer = 0;
        while outer < 3 {
            let mut inner = 0;
            invariant!(outer >= 0 && outer < 3);
            while inner < 3 {
                invariant!(inner >= 0 && inner < 3);
                inner += 1;
            }
            outer += 1;
        }

        // Inductive step rejects: range constraints not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

/// Break loop invariant: `i >= 0` (signed i32) fails inductive step (#1609).
#[test]
fn test_loop_with_break() {
    common::with_clean_verification(|| {
        // Declare variable to the verification context
        verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Add assumption about initial value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        // Invariant with early exit
        let mut i = 0;
        while i < 100 {
            invariant!(i >= 0);
            if i == 50 {
                break;
            }
            i += 1;
        }

        // Inductive step rejects: i >= 0 not universally valid for signed i32 (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

/// Continue loop invariant: `i >= 0` (signed i32) fails inductive step (#1609).
#[test]
fn test_loop_with_continue() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("sum".to_string(), "i32".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "sum_init".to_string(),
            "sum == 0".to_string(),
            None,
        );

        // Invariant with continue - sum accumulates odd numbers
        let mut i = 0;
        let mut sum = 0;
        while i < 10 {
            invariant!(i >= 0);
            i += 1;
            if i % 2 == 0 {
                continue;
            }
            sum += i;
        }
        // Verify sum was computed (1+3+5+7+9 = 25)
        assert_eq!(sum, 25);

        // Inductive step rejects: i >= 0 not universally valid for signed i32 (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}
