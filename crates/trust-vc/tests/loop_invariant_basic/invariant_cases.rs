// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// invariant! tests
// ============================================================================
#[test]
fn test_invariant_compiles() {
    common::with_clean_verification(|| {
        // Declare the variable to the verification context
        verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        // Basic invariant in a loop
        let mut i = 0;
        while i < 10 {
            invariant!(i >= 0);
            i += 1;
        }

        // Inductive step rejects: i >= 0 is not universally valid for signed i32 (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant (i >= 0, signed i32) should fail inductive step, got: {:?}",
            result
        );
    })
}

/// Multiple invariants: first non-tautological invariant fails inductive step (#1609).
///
/// `i >= 0` (signed i32) is not universally valid. The inductive step rejects
/// the first invariant before the second one is checked.
#[test]
fn test_invariant_multiple() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 10".to_string(),
            None,
        );

        // Multiple invariants in same loop
        let mut i = 0;
        let n = 10;
        while i < n {
            invariant!(i >= 0);
            invariant!(i <= n);
            i += 1;
        }

        // Inductive step rejects first invariant: i >= 0 not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant (i >= 0, signed i32) should fail inductive step, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invariant_with_expression() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context (use same width to avoid mismatch)
        verify_macro::collect_variable("_sum".to_string(), "i64".to_string());
        verify_macro::collect_variable("i".to_string(), "i64".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "_sum_init".to_string(),
            "_sum == 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        // Invariant with a compound expression. Keep this linear so the test
        // exercises rejection without depending on nonlinear solver timing.
        let mut _sum = 0i64;
        let mut i = 0;
        while i < 5 {
            invariant!(_sum == i + 1 || i == 0);
            _sum += i;
            i += 1;
        }

        // Inductive step rejects: complex expression not universally valid (#1609).
        // The publish-shaped solver path can reject via either a concrete
        // counterexample or an Unknown classification; both are sound rejections.
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "Non-tautological invariant should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invariant_boolean_ops() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("i".to_string(), "i32".to_string());
        verify_macro::collect_variable("_low".to_string(), "i32".to_string());
        verify_macro::collect_variable("high".to_string(), "i32".to_string());

        // Add assumptions about initial values
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "_low_value".to_string(),
            "_low == 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "high_value".to_string(),
            "high == 10".to_string(),
            None,
        );

        // Boolean operations in invariant
        let mut i = 0;
        let _low = 0;
        let high = 10;
        while i < high {
            invariant!(i >= _low && i < high);
            i += 1;
        }

        // Inductive step rejects: i >= _low && i < high not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

/// Array reference invariant: `i <= 5` (usize=u64) is not universally valid (#1609).
///
/// Even though usize is unsigned, `i <= 5` is not a tautology — counterexample: i = 6.
#[test]
fn test_invariant_references() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("i".to_string(), "usize".to_string());
        verify_macro::collect_variable("arr".to_string(), "Seq<i32>".to_string());

        // Add assumption about initial value
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_init".to_string(),
            "i == 0".to_string(),
            None,
        );

        // WORKAROUND: arr.len() parsing not yet supported; use a constant for now
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "arr_len_is_5".to_string(),
            "5 == 5".to_string(), // Trivial assumption to keep test structure
            None,
        );

        // Invariant referencing array
        let arr = [1, 2, 3, 4, 5];
        let mut i = 0;
        while i < arr.len() {
            // WORKAROUND: Use constant instead of arr.len() until #1191 is fixed
            invariant!(i <= 5);
            let _ = arr[i];
            i += 1;
        }

        // Inductive step rejects: i <= 5 not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant (i <= 5) should fail inductive step, got: {:?}",
            result
        );
    })
}
