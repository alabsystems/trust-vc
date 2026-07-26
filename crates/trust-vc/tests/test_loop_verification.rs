// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test that loop invariants and decreases measures collect AND VERIFY conditions.
//!
//! Issue #825: Loop invariant and decreases macros don't collect verification conditions
//! Issue #908: Test files must actually invoke ay verification
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::{invariant, loop_decreases};
use trust_vc_core::vc::{ObligationKind, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;
#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;

fn assert_loop_decreases_artifacts(context: &VerificationContext) {
    assert!(
        !context.obligations().is_empty(),
        "loop_decreases! should collect obligations"
    );

    let has_non_negative = context
        .obligations()
        .iter()
        .any(|o| matches!(o.kind(), ObligationKind::MeasureNonNegative));
    assert!(
        has_non_negative,
        "Should have collected non-negativity obligation, obligations: {:?}",
        context.obligations()
    );

    let has_decrease = context
        .obligations()
        .iter()
        .any(|o| matches!(o.kind(), ObligationKind::MeasureDecreases));
    assert!(
        has_decrease,
        "Should have collected decrease obligation, obligations: {:?}",
        context.obligations()
    );

    let has_entry_var = context.variables().iter().any(|v| v.name == "n_entry");
    assert!(
        has_entry_var,
        "Should have declared n_entry variable for decrease checking"
    );
}

fn collect_loop_decreases_body_semantics() {
    trust_vc_core::verify_macro::collect_obligation(
        ObligationKind::Assume,
        "loop_guard".to_string(),
        "n > 0".to_string(),
        None,
    );
    trust_vc_core::verify_macro::collect_obligation(
        ObligationKind::Assume,
        "body_decrement".to_string(),
        "n_entry == n + 1".to_string(),
        None,
    );
}

#[test]
fn test_invariant_collects_obligation() {
    common::with_clean_verification(|| {
        // Declare variable for ay
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Assume precondition: i starts in range [0, 5]
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_bounded".to_string(),
            "i >= 0 && i <= 5".to_string(),
            None,
        );

        // Use invariant! macro
        let mut i = 0;
        while i < 5 {
            invariant!(i >= 0 && i <= 5);
            i += 1;
        }

        // Check that we collected an obligation
        let context =
            trust_vc_core::verify_macro::get_context().expect("Should have verification context");

        assert!(
            !context.obligations().is_empty(),
            "invariant! should collect at least one obligation"
        );

        // Check that the obligation contains our invariant condition
        let has_invariant = context
            .obligations()
            .iter()
            .any(|o| o.condition().contains("i >= 0") && o.condition().contains("i <= 5"));

        assert!(
            has_invariant,
            "Should have collected the invariant condition, obligations: {:?}",
            context.obligations()
        );

        // CRITICAL FIX #908: Actually verify the collected obligations!
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // With inductive step (#1609), invariant i >= 0 && i <= 5 is checked
        // for universal validity via havoc. It's not a tautology (counterexample:
        // i = -1), so the inductive step rejects it.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step (#1609), got: {:?}",
            result
        );
    })
}

#[test]
fn test_loop_decreases_collects_obligations() {
    common::with_clean_verification(|| {
        // Declare variable for ay with proper type
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Assume n starts at 10 (precondition, not assertion)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_initial".to_string(),
            "n == 10".to_string(),
            None,
        );

        // Use loop_decreases! macro
        let mut n = 10;
        while n > 0 {
            loop_decreases!(n);
            n -= 1;
        }

        // Check that we collected obligations
        let context =
            trust_vc_core::verify_macro::get_context().expect("Should have verification context");
        assert_loop_decreases_artifacts(&context);

        // Model the loop body: n > 0 (guard) and n_entry == n + 1 (body did n = n_entry - 1).
        // This encodes the decrement semantics rather than assuming the conclusion.
        // Issue #1570: the old assumption "n_entry > n" was the conclusion itself (tautology).
        collect_loop_decreases_body_semantics();

        // Verify: n < n_entry follows from n_entry == n + 1 (not a tautology)
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert_eq!(
            result,
            VerifyResult::Verified,
            "Loop decreases should verify from loop body semantics (n_entry == n + 1)"
        );
    })
}

#[test]
fn test_invalid_invariant_collected() {
    common::with_clean_verification(|| {
        // Declare variable for ay
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Assume i is not 0 (so the invariant i == 0 will fail)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_not_zero".to_string(),
            "i == 5".to_string(),
            None,
        );

        // Collect an invariant that is invalid given the precondition
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "loop_invariant".to_string(),
            "i == 0".to_string(), // False when i == 5
            None,
        );

        // Verify the obligation was collected
        let context = trust_vc_core::verify_macro::get_context().expect("Should have context");

        assert!(
            !context.obligations().is_empty(),
            "Should have collected the invalid invariant"
        );

        let has_invariant = context
            .obligations()
            .iter()
            .any(|o| o.name() == "loop_invariant");

        assert!(
            has_invariant,
            "Should have the specific invariant collected, obligations: {:?}",
            context.obligations()
        );

        // CRITICAL FIX #908: Actually verify — invalid invariant should be rejected
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invalid invariant (i == 0 when i == 5) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_decreases_measure_rejected() {
    common::with_clean_verification(|| {
        // Declare variable for ay with negative initial value
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Assume n is -5 (negative value should fail non-negativity check)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_initial".to_string(),
            "n == -5".to_string(),
            None,
        );

        // Collect non-negativity obligation for n
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureNonNegative,
            "n_nonneg".to_string(),
            "(n) >= 0".to_string(),
            None,
        );

        // CRITICAL FIX #908: Actually verify the collected obligations!
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // The decreases measure should FAIL verification when n is negative
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Negative decreases measure should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multiple_invariants() {
    common::with_clean_verification(|| {
        // Declare variables for ay
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("_sum".to_string(), "i32".to_string());

        // Assume preconditions for the invariants to hold
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "i_in_range".to_string(),
            "i >= 0 && i <= 10".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "sum_nonneg".to_string(),
            "_sum >= 0".to_string(),
            None,
        );

        let mut i = 0;
        let mut _sum = 0;
        while i < 10 {
            invariant!(i >= 0);
            invariant!(i <= 10);
            invariant!(_sum >= 0);
            _sum += i;
            i += 1;
        }

        let context = trust_vc_core::verify_macro::get_context().expect("Should have context");

        // Should have collected all three invariants (per iteration)
        assert!(
            context.obligations().len() >= 3,
            "Should collect multiple invariants, got: {}",
            context.obligations().len()
        );

        // CRITICAL FIX #908: Actually verify the collected obligations!
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Inductive step (#1609) rejects: i >= 0 not universally valid for signed i32
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step (#1609), got: {:?}",
            result
        );
    })
}

#[test]
fn test_decreases_with_complex_measure() {
    common::with_clean_verification(|| {
        // Declare variables with initial values
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("y".to_string(), "i32".to_string());

        // Assume initial conditions (precondition, not assertion)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "initial_values".to_string(),
            "x == 10 && y == 5".to_string(),
            None,
        );

        let mut x = 10;
        let mut y = 5;
        while x > 0 || y > 0 {
            loop_decreases!(x + y);
            if x > 0 {
                x -= 1;
            } else {
                y -= 1;
            }
        }

        let context = trust_vc_core::verify_macro::get_context().expect("Should have context");

        // Check that we collected the complex measure (non-negativity)
        let has_measure = context
            .obligations()
            .iter()
            .any(|o| o.condition().contains("x + y"));

        assert!(has_measure, "Should collect complex decreases measure");

        // Check for decrease obligation (new: #825)
        let has_decrease = context.obligations().iter().any(|o| {
            matches!(
                o.kind(),
                trust_vc_core::vc::ObligationKind::MeasureDecreases
            )
        });

        assert!(
            has_decrease,
            "Should have collected decrease obligation for complex measure"
        );

        // Model the loop body: one of x or y decreases by 1 each iteration.
        // Entry var is "x_plus_y_entry" (sanitize_measure_name maps "x + y").
        // Issue #1570: old assumption "x___y_entry > x + y" was the conclusion (tautology).
        // Instead, model: loop guard (x > 0 || y > 0) and body decremented sum by 1.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "x > 0 || y > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_decrement".to_string(),
            "x_plus_y_entry == x + y + 1".to_string(),
            None,
        );

        // Verify: x + y < x_plus_y_entry follows from body decrement (not tautology)
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert_eq!(
            result,
            VerifyResult::Verified,
            "Complex decreases measure should verify from loop body semantics"
        );
    })
}

#[test]
fn test_lexicographic_decreases_measure() {
    common::with_clean_verification(|| {
        // Declare variables for lexicographic measure
        trust_vc_core::verify_macro::collect_variable("outer".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("inner".to_string(), "i32".to_string());

        // Assume initial conditions (precondition)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "initial_lex".to_string(),
            "outer == 3 && inner == 2".to_string(),
            None,
        );

        // Collect lexicographic loop decreases measure (with decrease checking)
        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "(outer, inner)".to_string(),
            Some("lexicographic_test".to_string()),
        );

        // Verify the lexicographic measure was collected
        let context = trust_vc_core::verify_macro::get_context().expect("Should have context");

        let has_lex_measure = context.obligations().iter().any(|o| {
            matches!(
                o.kind(),
                trust_vc_core::vc::ObligationKind::MeasureDecreases
            )
        });

        assert!(
            has_lex_measure,
            "Should have collected lexicographic decreases measure"
        );

        // Model BOTH components decreasing (outer AND inner each decrease by 1).
        // NOTE: This masks #1593 — the code generates per-component conjunctive constraints
        // instead of proper lexicographic disjunction. Because BOTH components decrease,
        // the per-component checks all pass. A proper lexicographic test would model
        // "outer decreases, inner unchanged" — see test_lexicographic_decreases_outer_only_regression_1593.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_guard".to_string(),
            "outer > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_body".to_string(),
            "outer_entry == outer + 1".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_body".to_string(),
            "inner_entry == inner + 1".to_string(),
            None,
        );

        // Verify: both outer < outer_entry and inner < inner_entry follow from body
        // semantics because BOTH decrease. This does NOT test lexicographic ordering.
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert_eq!(
            result,
            VerifyResult::Verified,
            "Lexicographic decreases should verify from loop body semantics"
        );
    })
}

#[test]
fn test_invariant_and_decreases_together() {
    common::with_clean_verification(|| {
        // Declare variable for ay
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Assume preconditions for the loop
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_bounded".to_string(),
            "n >= 0 && n <= 10".to_string(),
            None,
        );

        let mut n = 10;
        while n > 0 {
            invariant!(n >= 0 && n <= 10);
            loop_decreases!(n);
            n -= 1;
        }

        let context = trust_vc_core::verify_macro::get_context().expect("Should have context");

        // Should have invariant, non-negativity, AND decrease obligations
        assert!(
            context.obligations().len() >= 3,
            "Should have invariant, non-neg, and decrease obligations, got: {}",
            context.obligations().len()
        );

        // Check for invariant
        let has_invariant = context
            .obligations()
            .iter()
            .any(|o| o.condition().contains("n >= 0") && o.condition().contains("n <= 10"));

        // Check for non-negativity
        let has_non_negative = context.obligations().iter().any(|o| {
            matches!(
                o.kind(),
                trust_vc_core::vc::ObligationKind::MeasureNonNegative
            )
        });

        // Check for decrease
        let has_decrease = context.obligations().iter().any(|o| {
            matches!(
                o.kind(),
                trust_vc_core::vc::ObligationKind::MeasureDecreases
            )
        });

        assert!(has_invariant, "Should have invariant");
        assert!(has_non_negative, "Should have non-negativity measure");
        assert!(has_decrease, "Should have decrease measure");

        // Model loop body: n > 0 (guard) and n_entry == n + 1 (body did n = n_entry - 1).
        // Issue #1570: old assumption "n_entry > n" was the conclusion (tautology).
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "n > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_decrement".to_string(),
            "n_entry == n + 1".to_string(),
            None,
        );

        // Verify: invariant (n >= 0 && n <= 10) + decrease (n < n_entry) from body semantics
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Inductive step (#1609) rejects invariant: n >= 0 && n <= 10 not universally valid
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant should fail inductive step (#1609), got: {:?}",
            result
        );
    })
}

/// Vacuous truth detector: checks whether #1579 engine fix + test body model
/// creates contradictory assumptions (n_entry == n AND n_entry == n + 1).
///
/// If assumptions are contradictory, even FALSE assertions verify. This test
/// adds an obviously false assertion after the standard decreases setup to
/// detect vacuous truth.
///
/// EXPECTED: If this test PASSES (VerifyResult::Verified), the assumptions are contradictory
/// and all other loop_decreases tests pass vacuously — not because the decrease holds.
#[test]
fn test_vacuous_truth_detector_1579() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i64".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "loop_guard".to_string(),
            "n >= 0".to_string(),
            None,
        );

        // This calls add_loop_decrease_obligations which declares n_entry as
        // a free variable with only n_entry >= 0 assumed (no n_entry == n constraint).
        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "n".to_string(),
            Some("vacuous_test".to_string()),
        );

        // The test body model adds: n_entry == n + 1 (consistent with n_entry >= 0)
        // No contradiction: n_entry is unconstrained except >= 0, and n + 1 >= 0 when n >= 0.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "body_decrement".to_string(),
            "n_entry == n + 1".to_string(),
            None,
        );

        // Add an obviously FALSE assertion: 0 == 1
        // If this verifies, we have vacuous truth (contradictory assumptions).
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "vacuous_detector".to_string(),
            "0 == 1".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // If assumptions are NOT contradictory, 0 == 1 should produce a counterexample.
        // If assumptions ARE contradictory, 0 == 1 will verify (vacuous truth).
        assert!(
            !matches!(result, VerifyResult::Verified),
            "VACUOUS TRUTH DETECTED: assumptions are contradictory, causing \
             0 == 1 to verify. Check that n_entry constraints from engine and \
             body model are consistent (not contradictory)."
        );
    })
}

/// Regression test for #1593: lexicographic loop decrease generates wrong constraints.
///
/// Models "outer decreases, inner unchanged" — the canonical lexicographic case.
/// With correct lexicographic ordering: (outer < outer_entry) is sufficient.
/// With buggy conjunctive ordering: inner < inner_entry also required, but inner == inner_entry.
///
/// #1593 FIXED (W2 763, b6c9d33): now passes with correct lexicographic disjunction.
#[test]
fn test_lexicographic_decreases_outer_only_regression_1593() {
    common::with_clean_verification(|| {
        // Declare variables for lexicographic measure
        trust_vc_core::verify_macro::collect_variable("outer".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("inner".to_string(), "i32".to_string());

        // Assume initial conditions
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "initial_lex".to_string(),
            "outer == 3 && inner == 2".to_string(),
            None,
        );

        // Collect lexicographic loop decreases measure
        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "(outer, inner)".to_string(),
            Some("lex_regression_1593".to_string()),
        );

        // Model: outer decreases by 1, inner UNCHANGED
        // This is the canonical lexicographic case that #1593 breaks.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_guard".to_string(),
            "outer > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_body".to_string(),
            "outer_entry == outer + 1".to_string(),
            None,
        );
        // Inner unchanged: inner_entry == inner (NOT inner + 1)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_body".to_string(),
            "inner_entry == inner".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #1593 fixed: lexicographic disjunction correctly generates
        // (outer < outer_entry) || (outer == outer_entry && inner < inner_entry)
        // so outer-only decrease is sufficient.
        assert!(
            matches!(result, VerifyResult::Verified),
            "Lexicographic with outer-only decrease should verify. Got: {:?}",
            result,
        );
    })
}

/// Negative test: both components of a lexicographic pair stay the same.
/// The verifier should reject this because neither component decreases.
/// Regression guard for #1593 — ensures lex disjunction is not trivially true.
#[test]
fn test_lexicographic_no_decrease_rejected_1593() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("outer".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("inner".to_string(), "i32".to_string());

        // Guard: both positive
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_guard".to_string(),
            "outer > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_guard".to_string(),
            "inner > 0".to_string(),
            None,
        );

        // Collect lex measure
        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "(outer, inner)".to_string(),
            Some("lex_no_decrease".to_string()),
        );

        // Body model: BOTH components unchanged (no decrease)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "outer_body".to_string(),
            "outer_entry == outer".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "inner_body".to_string(),
            "inner_entry == inner".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Lex condition: outer < outer_entry || (outer == outer_entry && inner < inner_entry)
        // With both unchanged: outer < outer (false) || (outer == outer && inner < inner) (false)
        // Should produce Counterexample, not Verified.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Lexicographic with no decrease should be rejected. Got: {:?}",
            result,
        );
    })
}

/// Vacuous truth detector for the lexicographic (tuple) path.
/// If assumptions are contradictory, even `0 == 1` verifies — detect that.
/// Companion to `test_vacuous_truth_detector_1579` which covers single-measure path.
#[test]
fn test_vacuous_truth_detector_lex_path() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("a".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("b".to_string(), "i32".to_string());

        // Guard
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_guard".to_string(),
            "a > 0".to_string(),
            None,
        );

        // Collect lex measure — this creates entry variables and assumptions
        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "(a, b)".to_string(),
            Some("vacuous_lex".to_string()),
        );

        // Consistent body model: a decreases, b unchanged
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_body".to_string(),
            "a_entry == a + 1".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_body".to_string(),
            "b_entry == b".to_string(),
            None,
        );

        // Canary: assert 0 == 1. If assumptions are contradictory, this verifies.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "vacuous_canary".to_string(),
            "0 == 1".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // If NOT vacuous, ay should find a counterexample for 0 == 1.
        // If vacuous (contradictory assumptions), result would be Verified — which is a bug.
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Vacuous truth detected in lex path! 0 == 1 should not verify. Got: {:?}",
            result,
        );
    })
}

/// Triple measure: only the outermost component decreases, middle and inner unchanged.
/// Exercises the FIRST disjunct of a 3-component lexicographic encoding.
/// Companion to `test_loop_decreases_lexicographic_triple` which tests innermost only.
#[test]
fn test_lexicographic_triple_outer_only_decreases() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("a".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("b".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("c".to_string(), "i32".to_string());

        // Guard
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_guard".to_string(),
            "a > 0".to_string(),
            None,
        );

        trust_vc_core::verify_macro::collect_loop_decreases_measure(
            "(a, b, c)".to_string(),
            Some("triple_outer_only".to_string()),
        );

        // Body model: only a decreases, b and c unchanged
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "a_body".to_string(),
            "a_entry == a + 1".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "b_body".to_string(),
            "b_entry == b".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "c_body".to_string(),
            "c_entry == c".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Lex condition: a < a_entry || (a == a_entry && b < b_entry) || (a == a_entry && b == b_entry && c < c_entry)
        // With a_entry == a + 1: first disjunct a < a + 1 is true. Verification succeeds.
        assert!(
            matches!(result, VerifyResult::Verified),
            "Triple lex with only outer decrease should verify via first disjunct. Got: {:?}",
            result,
        );
    })
}
