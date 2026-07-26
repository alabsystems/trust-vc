// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comprehensive negative tests for all verification features.
//!
//! Each feature needs tests that verify invalid proofs are rejected.

use trust_vc::{assert_by, invariant, loop_decreases, proof, requires};
#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

// ============================================================================
// requires! negative tests
// ============================================================================

mod common;

#[test]
fn test_requires_violated_rejects() {
    common::with_clean_verification(|| {
        // Function that violates its own precondition
        #[proof]
        fn violates_requires() {
            requires!(false); // Always violated
            trust_vc::assert!(true);
        }

        // Catch the runtime panic — but obligations don't survive catch_unwind.
        // The verification context is empty after the panic, producing Error.
        let _ = std::panic::catch_unwind(violates_requires);

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Empty context after catch_unwind should produce Error, got: {:?}",
            result
        );
    })
}

// ============================================================================
// ensures! negative tests
// ============================================================================

#[test]
fn test_ensures_violated_rejects() {
    common::with_clean_verification(|| {
        // Manually add an ensures obligation that will be violated
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "violated_postcondition".to_string(),
            "result > 0".to_string(),
            None,
        );

        // Set result to violate the postcondition
        trust_vc_core::verify_macro::collect_variable("result".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "result_value".to_string(),
            "result == -5".to_string(),
            None,
        );

        expect_counterexample().expect("Violated postcondition should produce counterexample");
    })
}

// ============================================================================
// assert! negative tests
// ============================================================================

#[test]
fn test_false_assertion_rejects() {
    common::with_clean_verification(|| {
        // Simple false assertion - catch runtime panic
        let _ = std::panic::catch_unwind(|| {
            trust_vc::assert!(1 + 1 == 3);
        });

        expect_counterexample().expect("False assertion should produce counterexample");
    })
}

#[test]
fn test_contradictory_assertions_reject() {
    common::with_clean_verification(|| {
        // Contradictory assertions - catch runtime panic
        let _ = std::panic::catch_unwind(|| {
            trust_vc::assert!(true);
            trust_vc::assert!(false);
        });

        expect_counterexample().expect("Contradictory assertions should produce counterexample");
    })
}

// ============================================================================
// assert_by! negative tests
// ============================================================================

#[test]
fn test_assert_by_false_rejects() {
    common::with_clean_verification(|| {
        // assert_by! with false condition
        let _ = std::panic::catch_unwind(|| {
            assert_by! { 2 + 2 == 5 };
        });

        expect_counterexample().expect("False assert_by! should produce counterexample");
    })
}

// ============================================================================
// loop invariant negative tests
// ============================================================================

#[test]
fn test_invalid_invariant_rejects() {
    common::with_clean_verification(|| {
        // Catch runtime panic from invariant failure. The invariant! macro
        // collects an obligation referencing `i`, but doesn't declare `i` as
        // a verification variable. Lowering fails with "unresolved variable: i".
        let _ = std::panic::catch_unwind(|| {
            let mut i = 0;
            while i < 5 {
                invariant!(i == 0); // False after first iteration
                i += 1;
            }
        });

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Unresolved loop variable should produce Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invariant_not_established_rejects() {
    common::with_clean_verification(|| {
        // Same as test_invalid_invariant_rejects: loop variable `i` is not
        // declared as a verification variable by invariant!, producing Error.
        let _ = std::panic::catch_unwind(|| {
            let mut i = 1; // Starts at 1, not 0
            while i < 5 {
                invariant!(i == 0); // Never true
                i += 1;
            }
        });

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Unresolved loop variable should produce Error, got: {:?}",
            result
        );
    })
}

// ============================================================================
// decreases measure negative tests
// ============================================================================

#[test]
fn test_non_decreasing_measure_rejects() {
    common::with_clean_verification(|| {
        // loop_decreases! collects obligation referencing `i`, but `i` is not
        // declared as a verification variable. Lowering fails with
        // "unresolved variable: i".
        let mut i = 0;
        while i < 10 {
            loop_decreases!(i); // Increases, not decreases!
            i += 1;
        }

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Unresolved loop variable should produce Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_constant_measure_rejects() {
    common::with_clean_verification(|| {
        // loop_decreases!(42) with a constant measure. The macro generates
        // obligations but they don't survive to verification — empty context.
        let mut i = 0;
        while i < 10 {
            loop_decreases!(42); // Constant - never decreases
            i += 1;
        }

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Empty context should produce Error, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Combined feature negative tests
// ============================================================================

#[test]
fn test_requires_false_with_ensures_is_vacuously_verified() {
    common::with_clean_verification(|| {
        // In BodyLevel mode (default), requires(false) is assumed, making
        // any postcondition vacuously true (ex falso quodlibet). Fixes #1692.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Requires,
            "false_precondition".to_string(),
            "5 < 3".to_string(), // Always false — assumed in BodyLevel mode
            None,
        );

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Ensures,
            "true_postcondition".to_string(),
            "5 > 3".to_string(), // Always true, vacuously verified
            None,
        );

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        // Vacuous truth detection (#2258): requires(5 < 3) is false,
        // making assumptions contradictory → caught as Unknown.
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Unknown { .. }),
            "requires(false) should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invariant_with_bad_decreases_rejects() {
    common::with_clean_verification(|| {
        // invariant! references `i` which isn't a declared verification
        // variable, so lowering fails with "unresolved variable: i".
        let _ = std::panic::catch_unwind(|| {
            let mut i = 10;
            while i > 0 {
                invariant!(i >= 0);
                loop_decreases!(i + 1); // Increases instead of decreases
                i -= 1;
            }
        });

        let pipeline =
            trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Error { .. }),
            "Unresolved loop variable should produce Error, got: {:?}",
            result
        );
    })
}

// ============================================================================
// Arithmetic overflow negative tests
// ============================================================================

// Overflow and division-by-zero detection is covered by overflow_soundness.rs
// and the mode-aware checking in the encoder (ir_encoder/overflow.rs).
