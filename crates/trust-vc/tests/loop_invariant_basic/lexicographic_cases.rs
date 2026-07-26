// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// Lexicographic loop_decreases! tests (Issue #39)
// ============================================================================
#[test]
fn test_loop_decreases_lexicographic_pair() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("outer".to_string(), "i64".to_string());
        verify_macro::collect_variable("inner".to_string(), "i64".to_string());

        // Model inductive step for inner loop: outer unchanged, inner decrements
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_guard".to_string(),
            "inner > 0".to_string(),
            None,
        );

        // Lexicographic measure with two values as tuple
        let mut outer: i64 = 3;
        let mut inner: i64;
        while outer > 0 {
            inner = 3;
            while inner > 0 {
                loop_decreases!((outer, inner));
                inner -= 1;
            }
            outer -= 1;
        }

        // Body model: outer unchanged (outer_entry == outer), inner decremented (inner_entry == inner + 1)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_unchanged".to_string(),
            "outer_entry == outer".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_decrement".to_string(),
            "inner_entry == inner + 1".to_string(),
            None,
        );

        // Verify lexicographic pair decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Lexicographic pair decreases should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_lexicographic_triple() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("a".to_string(), "i64".to_string());
        verify_macro::collect_variable("b".to_string(), "i64".to_string());
        verify_macro::collect_variable("c".to_string(), "i64".to_string());

        // Model inductive step for innermost loop: a,b unchanged, c decrements
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "c_guard".to_string(),
            "c > 0".to_string(),
            None,
        );

        // Three-element lexicographic measure as tuple
        let mut a: i64 = 2;
        let mut b: i64;
        let mut c: i64;
        while a > 0 {
            b = 2;
            while b > 0 {
                c = 2;
                while c > 0 {
                    loop_decreases!((a, b, c));
                    c -= 1;
                }
                b -= 1;
            }
            a -= 1;
        }

        // Body model: a,b unchanged, c decremented by 1
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_unchanged".to_string(),
            "a_entry == a".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_unchanged".to_string(),
            "b_entry == b".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "c_decrement".to_string(),
            "c_entry == c + 1".to_string(),
            None,
        );

        // Verify lexicographic triple decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Lexicographic triple decreases should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_lexicographic_expressions() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        // Measures: (n - i, m - j); entry vars: n_minus_i_entry, m_minus_j_entry
        verify_macro::collect_variable("n".to_string(), "i64".to_string());
        verify_macro::collect_variable("m".to_string(), "i64".to_string());
        verify_macro::collect_variable("i".to_string(), "i64".to_string());
        verify_macro::collect_variable("j".to_string(), "i64".to_string());

        // Model inductive step for inner loop: j < m (inner guard)
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_guard".to_string(),
            "j < m".to_string(),
            None,
        );

        // Lexicographic with expressions, not just variables
        let n = 5i64;
        let m = 5i64;
        let mut i = 0i64;
        let mut j: i64;
        while i < n {
            j = 0;
            while j < m {
                loop_decreases!((n - i, m - j));
                j += 1;
            }
            i += 1;
        }

        // Body model: inner loop does j += 1, so (m-j) decreases by 1; (n-i) unchanged
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "first_unchanged".to_string(),
            "n_minus_i_entry == n - i".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "second_decrement".to_string(),
            "m_minus_j_entry == m - j + 1".to_string(),
            None,
        );

        // Verify lexicographic expression decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Lexicographic expression decreases should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_lexicographic_with_invariant() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("outer".to_string(), "i64".to_string());
        verify_macro::collect_variable("inner".to_string(), "i64".to_string());

        // Model inductive step for inner loop with invariants
        // Inductive hypothesis: assume invariants hold at loop entry
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_guard".to_string(),
            "inner > 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_positive".to_string(),
            "outer > 0".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_le_outer".to_string(),
            "inner <= outer".to_string(),
            None,
        );

        // Combine lexicographic decreases with invariants
        let mut outer = 3i64;
        let mut inner: i64;
        while outer > 0 {
            invariant!(outer >= 0);
            inner = outer;
            while inner > 0 {
                invariant!(inner >= 0);
                invariant!(inner <= outer);
                loop_decreases!((outer, inner));
                inner -= 1;
            }
            outer -= 1;
        }

        // Body model: outer unchanged, inner decremented by 1
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_unchanged".to_string(),
            "outer_entry == outer".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_decrement".to_string(),
            "inner_entry == inner + 1".to_string(),
            None,
        );

        // Inductive step rejects invariants: outer >= 0, inner >= 0 not universally valid (#1609)
        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step, got: {:?}",
            result
        );
    })
}

#[test]
fn test_loop_decreases_lexicographic_unsigned() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("x".to_string(), "u64".to_string());
        verify_macro::collect_variable("y".to_string(), "u64".to_string());

        // Model inductive step for inner loop: y decrements, x unchanged
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_guard".to_string(),
            "y > 0".to_string(),
            None,
        );

        // Lexicographic with unsigned types
        let mut x: u64 = 4;
        let mut y: u64;
        while x > 0 {
            y = 4;
            while y > 0 {
                loop_decreases!((x, y));
                y -= 1;
            }
            x -= 1;
        }

        // Body model: x unchanged, y decremented
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_unchanged".to_string(),
            "x_entry == x".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_decrement".to_string(),
            "y_entry == y + 1".to_string(),
            None,
        );

        // Verify unsigned lexicographic decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Unsigned lexicographic decreases should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_lexicographic_mixed_types() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("a".to_string(), "i64".to_string());
        verify_macro::collect_variable("b".to_string(), "i64".to_string());

        // Model inductive step for inner loop: b decrements, a unchanged
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_guard".to_string(),
            "b > 0".to_string(),
            None,
        );

        // Mixed types in lexicographic tuple (both coerce to comparable)
        let mut a: i64 = 3;
        let mut b: i64;
        while a > 0 {
            b = 5;
            while b > 0 {
                loop_decreases!((a, b));
                b -= 1;
            }
            a -= 1;
        }

        // Body model: a unchanged, b decremented
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_unchanged".to_string(),
            "a_entry == a".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_decrement".to_string(),
            "b_entry == b + 1".to_string(),
            None,
        );

        // Verify mixed type lexicographic decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Mixed type lexicographic decreases should verify"
            ),
        }
    })
}

#[test]
fn test_loop_decreases_lexicographic_single_outer_loop() {
    common::with_clean_verification(|| {
        // Declare variables to the verification context
        verify_macro::collect_variable("m".to_string(), "i64".to_string());
        verify_macro::collect_variable("n".to_string(), "i64".to_string());

        // Model inductive step: when n > 0, m unchanged and n decrements
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_guard".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Lexicographic in a single loop with two counters
        let mut m: i64 = 3;
        let mut n: i64 = 3;
        while m > 0 || n > 0 {
            loop_decreases!((m, n));
            if n > 0 {
                n -= 1;
            } else {
                m -= 1;
                n = 3;
            }
        }

        // Body model for n > 0 branch: m unchanged, n decremented
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "m_unchanged".to_string(),
            "m_entry == m".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_decrement".to_string(),
            "n_entry == n + 1".to_string(),
            None,
        );

        // Verify single loop lexicographic decreases was collected and is valid
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Single loop lexicographic decreases should verify"
            ),
        }
    })
}
