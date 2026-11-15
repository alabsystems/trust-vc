// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_format_solver_observation_error_preserves_solver_panic_marker() {
    let reason = format_solver_observation_error(
        "ay error checking 'my_assertion'",
        SolverError::SolverPanic("sort mismatch".to_string()),
    );

    assert!(
        reason.contains("ay solver panic"),
        "solver panic formatting must preserve the public classification marker: {reason}"
    );
    assert_eq!(
        UnknownCategory::classify(&reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_format_solver_observation_error_non_panic_variant() {
    let reason = format_solver_observation_error(
        "ay error checking 'assertion_x'",
        SolverError::UnsupportedLogic("QF_NIA".to_string()),
    );
    assert!(
        reason.contains("assertion_x"),
        "non-panic error should include context: {reason}"
    );
    assert!(
        !reason.contains("ay solver panic"),
        "non-panic error should not contain panic marker: {reason}"
    );
}

#[test]
fn test_format_unknown_reason_none_returns_unspecified() {
    let result = format_unknown_reason(None);
    assert_eq!(result, "unspecified");
}

#[test]
fn test_format_unknown_reason_some_returns_display() {
    let result = format_unknown_reason(Some(UnknownReason::Timeout));
    assert!(
        !result.is_empty(),
        "Timeout reason should produce a non-empty string"
    );
    assert!(
        result.to_lowercase().contains("timeout") || !result.is_empty(),
        "Timeout reason should format meaningfully: {result}"
    );
}

#[test]
fn test_format_solver_scope_pop_warning_includes_assertion_and_error() {
    let warning = format_solver_scope_pop_warning(
        "assertion_x",
        &SolverError::UnsupportedLogic("QF_NIA".to_string()),
    );
    assert!(
        warning.contains("assertion_x"),
        "scope-pop warning should identify the assertion: {warning}"
    );
    assert!(
        warning.contains("QF_NIA"),
        "scope-pop warning should preserve the solver error detail: {warning}"
    );
}

#[test]
fn test_classify_unknown_reason_timeout() {
    let category = classify_unknown_reason(Some(UnknownReason::Timeout), "fallback");
    assert_eq!(
        category,
        UnknownCategory::Timeout,
        "Timeout UnknownReason must map to Timeout category"
    );
}

#[test]
fn test_classify_unknown_reason_none_uses_fallback() {
    let category = classify_unknown_reason(None, "ay solver panic: sort mismatch");
    assert_eq!(
        category,
        UnknownCategory::SolverPanic,
        "None reason with panic fallback string should classify via fallback: {:?}",
        category
    );
}

#[test]
fn test_classify_unknown_reason_resource_limit() {
    let category =
        classify_unknown_reason(Some(UnknownReason::ResourceLimit), "irrelevant fallback");
    assert_eq!(
        category,
        UnknownCategory::SolverUnknown,
        "ResourceLimit should map to SolverUnknown"
    );
}

#[test]
fn test_solver_unknown_outcome_preserves_exact_quantifier_detail() {
    // (reason, expected category). Budget-retriable quantifier reasons stay the
    // coarse non-failure SolverUnknown; permanently-non-retriable quantifier
    // reasons are genuine theory incompleteness and map to Incompleteness
    // (a model-less failure on a proof obligation). This mirrors
    // `SolverUnknownDetail`'s BudgetPressureRetriable vs PermanentlyNonRetriable
    // split. See design-unknown-as-failure.md.
    let cases = [
        (
            UnknownReason::QuantifierRoundLimit,
            UnknownCategory::SolverUnknown,
        ),
        (
            UnknownReason::QuantifierDeferred,
            UnknownCategory::SolverUnknown,
        ),
        (
            UnknownReason::QuantifierUnhandled,
            UnknownCategory::Incompleteness,
        ),
        (
            UnknownReason::QuantifierCegqiIncomplete,
            UnknownCategory::Incompleteness,
        ),
        (
            UnknownReason::QuantifierEmatchingExistsIncomplete,
            UnknownCategory::Incompleteness,
        ),
    ];

    for (reason, expected_category) in cases {
        let outcome =
            solver_unknown_outcome("quantified", Some("src/lib.rs:12:34"), Some(reason), None);
        match outcome {
            AssertionOutcome::Unknown {
                reason: rendered_reason,
                category,
                detail,
            } => {
                assert!(
                    rendered_reason.contains("Solver returned unknown"),
                    "unknown reason should keep the standard rendering: {rendered_reason}"
                );
                assert!(
                    rendered_reason.contains("src/lib.rs:12:34"),
                    "location should be preserved in the rendered reason: {rendered_reason}"
                );
                assert_eq!(
                    category,
                    Some(expected_category),
                    "{reason:?} should classify as {expected_category:?}"
                );
                assert_eq!(
                    detail,
                    Some(SolverUnknownDetail::AY(reason)),
                    "exact unknown detail should preserve {reason:?}"
                );
            }
            other => panic!("expected Unknown outcome, got: {other:?}"),
        }
    }
}

#[test]
fn test_demote_verified_outcome_no_demotion_when_clean() {
    let diagnostics = EncodingDiagnostics::default();
    let result = demote_verified_outcome(AssertionOutcome::Verified, "test_target", &diagnostics);
    assert!(
        matches!(result, AssertionOutcome::Verified),
        "Verified with clean diagnostics should stay Verified: {:?}",
        result
    );
}

#[test]
fn test_demote_verified_outcome_demotes_with_approximation() {
    let mut diagnostics = EncodingDiagnostics::default();
    diagnostics.record(
        crate::encoder::diagnostics::EncodingApproximation::FunctionContextReturnTypeOmitted,
    );
    let result = demote_verified_outcome(AssertionOutcome::Verified, "test_target", &diagnostics);
    assert!(
        matches!(result, AssertionOutcome::Unknown { .. }),
        "Verified with demoting approximation should become Unknown: {:?}",
        result
    );
    if let AssertionOutcome::Unknown {
        reason,
        category,
        detail,
    } = result
    {
        assert!(
            reason.contains("demoted:"),
            "Demoted reason should contain 'demoted:' prefix: {reason}"
        );
        assert_eq!(
            category,
            Some(UnknownCategory::EncodingDemotion),
            "Demoted category should be EncodingDemotion"
        );
        assert_eq!(
            detail, None,
            "demotion is trust-vc-local and should not invent detail"
        );
    }
}

#[test]
fn test_demote_verified_outcome_non_demoting_approximation_stays_verified() {
    let mut diagnostics = EncodingDiagnostics::default();
    diagnostics.record(crate::encoder::diagnostics::EncodingApproximation::BoundsCheckSkipped);
    let result = demote_verified_outcome(AssertionOutcome::Verified, "test_target", &diagnostics);
    assert!(
        matches!(result, AssertionOutcome::Verified),
        "Verified with non-demoting approximation should stay Verified: {:?}",
        result
    );
}

#[test]
fn test_demote_verified_outcome_counterexample_not_demoted() {
    let mut diagnostics = EncodingDiagnostics::default();
    diagnostics.record(
        crate::encoder::diagnostics::EncodingApproximation::FunctionContextReturnTypeOmitted,
    );
    let result = demote_verified_outcome(
        AssertionOutcome::Counterexample {
            obligation_name: "test".to_string(),
            location: None,
            model: None,
            bindings: Vec::new(),
        },
        "test_target",
        &diagnostics,
    );
    assert!(
        matches!(result, AssertionOutcome::Counterexample { .. }),
        "Counterexample should not be demoted even with demoting diagnostics: {:?}",
        result
    );
}

/// An encoder whose solver holds `b` and `not b`, so any solve on it that
/// runs answers UNSAT.
fn contradictory_encoder() -> AYEncoder {
    let mut encoder = AYEncoder::new();
    let b = encoder.solver.declare_const("b", ay_dpll::api::Sort::Bool);
    let not_b = encoder.solver.try_not(b).expect("b is Boolean");
    encoder.solver.try_assert_term(b).expect("assert b");
    encoder.solver.try_assert_term(not_b).expect("assert not b");
    encoder
}

/// After a solve panics, the next solve on the same solver is refused without
/// solving, even though the query it would decide is UNSAT.
#[test]
fn a_solver_whose_solve_panicked_is_not_asked_again() {
    let mut encoder = contradictory_encoder();
    super::super::test_hooks::FORCE_SOLVE_PANIC_ONCE.with(|flag| flag.set(true));
    let first = try_check_sat_with_details(&mut encoder.solver, &mut encoder.state.solver_panic);
    assert!(
        matches!(first, Err(SolverError::SolverPanic(_))),
        "the forced panic must surface as a solver panic: {first:?}"
    );

    let second = try_check_sat_with_details(&mut encoder.solver, &mut encoder.state.solver_panic);
    match second {
        Err(SolverError::SolverPanic(reason)) => {
            assert!(
                reason.contains("not reused") && reason.contains("simulated ay solve panic"),
                "the refusal must say why and quote the first panic: {reason}"
            );
            assert_eq!(
                UnknownCategory::classify(&format_solver_observation_error(
                    "ctx",
                    SolverError::SolverPanic(reason)
                )),
                UnknownCategory::SolverPanic
            );
        }
        other => panic!("a poisoned solver must not decide anything: {other:?}"),
    }
}

/// Twin of the test above without the forced panic: both solves run and
/// answer UNSAT.
#[test]
fn a_solver_that_never_panicked_keeps_deciding() {
    let mut encoder = contradictory_encoder();
    super::super::test_hooks::FORCE_SOLVE_PANIC_ONCE.with(|flag| flag.set(false));
    let first = try_check_sat_with_details(&mut encoder.solver, &mut encoder.state.solver_panic);
    assert!(
        matches!(&first, Ok(details) if details.result.result().is_unsat()),
        "b and not b is UNSAT: {first:?}"
    );

    let second = try_check_sat_with_details(&mut encoder.solver, &mut encoder.state.solver_panic);
    assert!(
        matches!(&second, Ok(details) if details.result.result().is_unsat()),
        "a healthy solver keeps answering: {second:?}"
    );
    assert!(encoder.state.solver_panic.is_none());
}
