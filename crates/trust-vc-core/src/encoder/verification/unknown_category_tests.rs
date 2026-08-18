// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// -- Classification tests using actual reason strings from the codebase --

#[test]
fn test_classify_timeout() {
    let reason =
        "Solver timed out after 10s for 'my_assertion' (BV solver timeout enforcement, #1605)";
    assert_eq!(UnknownCategory::classify(reason), UnknownCategory::Timeout);
}

#[test]
fn test_classify_solver_panic_from_panic_rs() {
    let reason = "ay solver panic: sort mismatch: expected Bool got BV32";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_solver_panic_from_assertion_rs() {
    let reason = "ay panic during encoding for 'overflow_check': BUG: mk_eq sort mismatch";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_solver_panic_inductive_step() {
    let reason = "ay panic during inductive step encoding for 'loop_inv': theory conflict";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_solver_panic_from_typed_assumption_sort_mismatch() {
    let reason = "encode typed assumption: Failed to encode assumption 'target_in_range': exists guard sort mismatch: expected Bool, got BV64";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_solver_panic_from_overflow_sort_mismatch() {
    let reason =
        "Failed to parse overflow checks for 'wrong_half': mk_eq sort mismatch: expects Bool, got Int";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_thread_panic() {
    let reason = "Solver thread panicked (non-ay) for 'my_assertion'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ThreadPanic
    );
}

#[test]
fn test_classify_confirmation_disagree() {
    let reason =
        "Confirmation check disagreed for 'my_assertion' — possible ay-dpll non-determinism (#2241)";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ConfirmationDisagree
    );
}

#[test]
fn test_classify_confirmation_disagree_inductive() {
    let reason =
        "Confirmation check disagreed for 'inv' (inductive step) — possible ay-dpll non-determinism (#2241)";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ConfirmationDisagree
    );
}

#[test]
fn test_classify_confirmation_encoder_error() {
    let reason = "Confirmation check encoder error for 'inv' (inductive step): parse error — re-verification setup failed";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ConfirmationDisagree
    );
}

#[test]
fn test_classify_confirmation_ay_panic() {
    let reason = "Confirmation check ay panic for 'inv' (inductive step): sort mismatch — solver panic during re-verification";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverPanic
    );
}

#[test]
fn test_classify_model_not_validated() {
    let reason = "sat model not validated by ay for overflow check 'add_overflow' in 'my_fn'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ModelNotValidated
    );
}

#[test]
fn test_classify_model_not_validated_main() {
    let reason = "sat model not validated by ay for 'my_assertion'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ModelNotValidated
    );
}

#[test]
fn test_classify_empty_model() {
    let reason = "Solver returned SAT with empty model for overflow check 'add' in 'fn' — treating as unknown (ay-dpll CEGQI limitation)";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::EmptyModel
    );
}

#[test]
fn test_classify_empty_model_main() {
    let reason = "Solver returned SAT with empty model for 'assertion' — treating as unknown (ay-dpll CEGQI limitation)";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::EmptyModel
    );
}

#[test]
fn test_classify_solver_unknown() {
    let reason = "Solver returned unknown (resource limit) for overflow check 'add' in 'fn'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverUnknown
    );
}

#[test]
fn test_classify_solver_unknown_main() {
    let reason = "Solver returned unknown (unspecified) for 'my_assertion'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverUnknown
    );
}

#[test]
fn test_classify_solver_unknown_lowercase_timeout_display() {
    let reason = "Solver returned unknown (timeout) for 'my_assertion'";
    assert_eq!(UnknownCategory::classify(reason), UnknownCategory::Timeout);
}

#[test]
fn test_classify_solver_unknown_quantifier_display() {
    let reason = "Solver returned unknown ((incomplete quantifier-round-limit)) for 'quantified'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::SolverUnknown
    );
}

#[test]
fn test_from_unknown_reason_timeout() {
    assert_eq!(
        UnknownCategory::from_unknown_reason(Some(UnknownReason::Timeout)),
        Some(UnknownCategory::Timeout)
    );
}

#[test]
fn test_from_unknown_reason_quantifier_round_limit() {
    assert_eq!(
        UnknownCategory::from_unknown_reason(Some(UnknownReason::QuantifierRoundLimit)),
        Some(UnknownCategory::SolverUnknown)
    );
}

#[test]
fn test_from_unknown_reason_unsupported_is_incompleteness() {
    // `Unsupported` is a genuine theory/fragment gap, not a resource limit:
    // more budget never closes it, so it maps to Incompleteness (a model-less
    // failure on a proof obligation). See design-unknown-as-failure.md.
    assert_eq!(
        UnknownCategory::from_unknown_reason(Some(UnknownReason::Unsupported)),
        Some(UnknownCategory::Incompleteness)
    );
}

#[test]
fn test_from_unknown_reason_incomplete_is_incompleteness() {
    // Nonlinear-arithmetic / NRA unknowns surface from ay as `Incomplete`; this
    // is the real_nonlinear2 class. They are genuine incompleteness, not a
    // resource limit, and must map to a verification failure.
    let category = UnknownCategory::from_unknown_reason(Some(UnknownReason::Incomplete)).unwrap();
    assert_eq!(category, UnknownCategory::Incompleteness);
    assert!(category.is_incompleteness());
    assert!(
        !category.is_retriable(),
        "incompleteness is never retriable"
    );
}

#[test]
fn test_from_unknown_reason_resource_reasons_are_not_incompleteness() {
    // The soundness boundary: resource/budget unknowns stay a non-failure
    // Unknown. A timeout does not mean the fact is false.
    for reason in [
        UnknownReason::Timeout,
        UnknownReason::ResourceLimit,
        UnknownReason::MemoryLimit,
        UnknownReason::Interrupted,
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
        UnknownReason::SplitLimit,
        UnknownReason::InternalError,
        // Neither of the next two is a resource limit, but both sit in the same
        // SolverUnknown arm and neither is ever an incompleteness FAILURE.
        // `ProofTrusted` was deleted by ay 0.6 (66538b006) and RESTORED at its
        // original spelling in ay 0.7, so the two gates — certification refuted
        // a verdict vs. strict proofs withheld an unsat — are distinct again.
        UnknownReason::SelfCheckRejected,
        UnknownReason::ProofTrusted,
        UnknownReason::Unknown,
    ] {
        let category = UnknownCategory::from_unknown_reason(Some(reason)).unwrap();
        assert!(
            !category.is_incompleteness(),
            "{reason:?} must NOT be classified as incompleteness (resource != false)"
        );
    }
}

#[test]
fn test_classify_encoding_demotion() {
    let reason = "demoted: encoding approximations [quantifier_fallback] for 'my_assertion'";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::EncodingDemotion
    );
}

#[test]
fn test_classify_opaque_types() {
    let reason =
        "Context contains variables with unrecognized types that cannot be soundly encoded: x: String. Verification skipped to prevent spurious results.";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::OpaqueTypes
    );
}

#[test]
fn test_classify_vacuous_truth() {
    let reason = "Assumptions are contradictory — all assertions would be vacuously true. Check requires/assume annotations for conflicting constraints.";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::VacuousTruth
    );
}

#[test]
fn test_classify_unsupported_mode() {
    let reason = "Solver mode 'nonlinear_arith' requested for 'my_fn' is not yet implemented — returning Unknown (fail-closed). Part of #2144.";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::UnsupportedMode
    );
}

#[test]
fn test_classify_other() {
    let reason = "some completely unrecognized reason";
    assert_eq!(UnknownCategory::classify(reason), UnknownCategory::Other);
}

// -- Helper method tests (exhaustive: every variant, every method) --

/// Exercises every `UnknownCategory` variant through all four classification
/// methods. Rows: (variant, retriable, soundness_relevant, solver_limitation,
/// incompleteness). If a new variant is added, this test must be updated.
///
/// The `incompleteness` column is the soundness-critical one: it must be `true`
/// for *exactly* `Incompleteness` (the should-fail direction — flips to a
/// model-less Counterexample, matching Verus `Invalid(None, None, None)`) and
/// `false` for every other variant (the should-not-fabricate-failure direction
/// — resource/timeout/panic Unknowns stay a non-failure Unknown). See
/// `design-unknown-as-failure.md`.
#[test]
fn test_helper_methods_exhaustive() {
    let cases: &[(UnknownCategory, bool, bool, bool, bool)] = &[
        // (variant,                         retriable, soundness, solver_lim, incompl)
        (UnknownCategory::Timeout, true, false, true, false),
        (UnknownCategory::SolverPanic, false, false, true, false),
        (UnknownCategory::ThreadPanic, false, false, false, false),
        (
            UnknownCategory::ConfirmationDisagree,
            false,
            true,
            false,
            false,
        ),
        (
            UnknownCategory::ModelNotValidated,
            false,
            true,
            false,
            false,
        ),
        (UnknownCategory::EmptyModel, false, false, true, false),
        (UnknownCategory::SolverUnknown, false, false, true, false),
        (UnknownCategory::Incompleteness, false, false, true, true),
        (UnknownCategory::EncodingDemotion, false, true, false, false),
        (UnknownCategory::OpaqueTypes, false, false, false, false),
        (UnknownCategory::VacuousTruth, false, true, false, false),
        (UnknownCategory::UnsupportedMode, false, false, false, false),
        (UnknownCategory::Other, false, false, false, false),
    ];
    for &(cat, retriable, soundness, solver_lim, incompl) in cases {
        assert_eq!(cat.is_retriable(), retriable, "{cat:?}.is_retriable()");
        assert_eq!(
            cat.is_soundness_relevant(),
            soundness,
            "{cat:?}.is_soundness_relevant()"
        );
        assert_eq!(
            cat.is_solver_limitation(),
            solver_lim,
            "{cat:?}.is_solver_limitation()"
        );
        assert_eq!(
            cat.is_incompleteness(),
            incompl,
            "{cat:?}.is_incompleteness()"
        );
    }
}

/// Should-FAIL direction: the genuine theory-incompleteness category is the
/// only variant that `is_incompleteness()` reports `true` for, so it is the
/// only one `verdict_from_result` flips into a model-less Counterexample
/// (Verus `Invalid(None, None, None)`). Pairs with
/// `test_is_incompleteness_false_for_every_resource_class_variant` below.
#[test]
fn test_is_incompleteness_true_only_for_incompleteness_variant() {
    assert!(
        UnknownCategory::Incompleteness.is_incompleteness(),
        "Incompleteness must report true so the gate surfaces a model-less failure"
    );
    // The NRA/real_nonlinear2 source: ay reports `Incomplete`, which classifies
    // to `Incompleteness`, which is the should-fail direction.
    let nra = UnknownCategory::from_unknown_reason(Some(UnknownReason::Incomplete)).unwrap();
    assert!(
        nra.is_incompleteness(),
        "NRA `Incomplete` is the real_nonlinear2 incompleteness should-fail case"
    );
}

/// Should-NOT-fabricate-failure direction: no resource/budget/timeout/panic
/// category may report `is_incompleteness()` — a resource limit does not mean
/// the fact is false, so it must never become a (model-less) failure. This is
/// the load-bearing soundness boundary opposite the should-fail case.
#[test]
fn test_is_incompleteness_false_for_every_resource_class_variant() {
    for cat in [
        UnknownCategory::Timeout,
        UnknownCategory::SolverPanic,
        UnknownCategory::ThreadPanic,
        UnknownCategory::ConfirmationDisagree,
        UnknownCategory::ModelNotValidated,
        UnknownCategory::EmptyModel,
        UnknownCategory::SolverUnknown,
        UnknownCategory::EncodingDemotion,
        UnknownCategory::OpaqueTypes,
        UnknownCategory::VacuousTruth,
        UnknownCategory::UnsupportedMode,
        UnknownCategory::Other,
    ] {
        assert!(
            !cat.is_incompleteness(),
            "{cat:?} must NOT be incompleteness — a non-incompleteness Unknown \
             must never be fabricated into a model-less verification failure"
        );
    }
}

#[test]
fn test_actionable_suggestions_are_non_empty_for_all_variants() {
    let cases = [
        UnknownCategory::Timeout,
        UnknownCategory::SolverPanic,
        UnknownCategory::ThreadPanic,
        UnknownCategory::ConfirmationDisagree,
        UnknownCategory::ModelNotValidated,
        UnknownCategory::EmptyModel,
        UnknownCategory::SolverUnknown,
        UnknownCategory::Incompleteness,
        UnknownCategory::EncodingDemotion,
        UnknownCategory::OpaqueTypes,
        UnknownCategory::VacuousTruth,
        UnknownCategory::UnsupportedMode,
        UnknownCategory::Other,
    ];
    for category in cases {
        assert!(
            !category.actionable_suggestion().is_empty(),
            "{category:?} should have a suggestion"
        );
    }
}

// -- VerifyResult integration tests --

#[test]
fn test_unknown_category_on_unknown_result() {
    let result = VerifyResult::unknown(
        "Solver timed out after 10s for 'test'",
        Some(UnknownCategory::Timeout),
    );
    assert_eq!(result.unknown_category(), Some(UnknownCategory::Timeout));
}

#[test]
fn test_unknown_category_on_lowercase_timeout_display() {
    let result = VerifyResult::unknown(
        "Solver returned unknown (timeout) for 'test'",
        Some(UnknownCategory::Timeout),
    );
    assert_eq!(result.unknown_category(), Some(UnknownCategory::Timeout));
}

#[test]
fn test_unknown_category_on_verified() {
    assert_eq!(VerifyResult::Verified.unknown_category(), None);
}

#[test]
fn test_unknown_category_on_counterexample() {
    let result = VerifyResult::Counterexample {
        obligation_name: "test".to_string(),
        model: None,
        bindings: Vec::new(),
    };
    assert_eq!(result.unknown_category(), None);
}

#[test]
fn test_unknown_category_on_error() {
    let result = VerifyResult::Error {
        message: "encoding failed".to_string(),
    };
    assert_eq!(result.unknown_category(), None);
}

// ---------------------------------------------------------------------------
// Unknown-as-failure routing (docs/design-unknown-as-failure.md)
//
// These pin the load-bearing soundness boundary: an INCOMPLETENESS unknown on a
// proof obligation becomes a model-less verification FAILURE (Verus's
// `Invalid(None, None, None)`), while a RESOURCE/timeout unknown stays a
// non-failure `Unknown` because more budget might still prove the fact.
// ---------------------------------------------------------------------------

#[test]
fn incompleteness_unknown_becomes_modelless_not_proved_failure() {
    let result = VerifyResult::unknown(
        "Solver returned unknown (incomplete) for 'test1_fails1' at src/lib.rs:7:5",
        Some(UnknownCategory::Incompleteness),
    );

    // It is a FAILURE, not an inconclusive outcome.
    assert!(result.is_not_proved(), "expected NotProved, got {result:?}");
    assert!(result.is_failure());
    assert!(!result.is_unknown());
    assert!(!result.is_verified());

    // ...and it is NOT a counterexample: no model was found, so none is claimed.
    assert!(!result.is_counterexample());

    // The variant is structurally model-less: destructuring proves there is no
    // `model` and no `bindings` field to populate at all.
    let VerifyResult::NotProved { reason, category } = &result else {
        panic!("expected NotProved, got {result:?}");
    };
    assert!(category.is_incompleteness());
    assert!(reason.contains("test1_fails1"));

    // The category still reaches diagnostics/triage.
    assert_eq!(
        result.unknown_category(),
        Some(UnknownCategory::Incompleteness)
    );
}

#[test]
fn resource_class_unknowns_never_become_failures() {
    // The whole resource/inconclusive family must stay `Unknown`. A timeout does
    // NOT mean the fact is false — reporting it as a failure would be unsound.
    let resource_categories = [
        UnknownCategory::Timeout,
        UnknownCategory::SolverUnknown,
        UnknownCategory::SolverPanic,
        UnknownCategory::ThreadPanic,
        UnknownCategory::ConfirmationDisagree,
        UnknownCategory::ModelNotValidated,
        UnknownCategory::EmptyModel,
        UnknownCategory::EncodingDemotion,
        UnknownCategory::OpaqueTypes,
        UnknownCategory::VacuousTruth,
        UnknownCategory::UnsupportedMode,
        UnknownCategory::Other,
    ];

    for category in resource_categories {
        let result = VerifyResult::unknown("solver gave up", Some(category));
        assert!(
            result.is_unknown(),
            "{category:?} must stay a non-failure Unknown, got {result:?}"
        );
        assert!(
            !result.is_not_proved() && !result.is_failure(),
            "{category:?} must never be promoted into a verification failure"
        );
    }
}

#[test]
fn timeout_unknown_stays_unknown_even_though_it_did_not_prove_the_goal() {
    let result = VerifyResult::unknown(
        "Solver timed out after 10s for 'slow_lemma'",
        Some(UnknownCategory::Timeout),
    );
    assert!(result.is_unknown());
    assert!(!result.is_failure());
    assert_eq!(result.unknown_category(), Some(UnknownCategory::Timeout));
}

#[test]
fn unclassified_reason_strings_cannot_be_promoted_into_failures() {
    // `classify` (the string fallback used when no structured category is
    // supplied) can never yield `Incompleteness`, so an unrecognized reason
    // fails OPEN to a soft Unknown rather than into a verification failure.
    for reason in [
        "some brand-new solver message nobody has seen",
        "Solver returned unknown (nra) for 'g'",
        "ay solver panic: sort mismatch",
        "Assumptions are contradictory — vacuously true",
    ] {
        assert_ne!(
            UnknownCategory::classify(reason),
            UnknownCategory::Incompleteness,
            "classify({reason:?}) must not yield Incompleteness"
        );
        let result = VerifyResult::unknown(reason, None);
        assert!(
            !result.is_failure(),
            "unclassified reason {reason:?} must not become a failure, got {result:?}"
        );
    }
}

#[test]
fn genuine_counterexample_still_carries_its_model_and_bindings() {
    // The mapping must not disturb real, model-bearing refutations.
    let result = VerifyResult::Counterexample {
        obligation_name: "ensures".to_string(),
        model: Some("x = -1".to_string()),
        bindings: vec![crate::verify_result::CounterexampleBinding::new(
            "x", "x", "i32", "-1",
        )],
    };

    assert!(result.is_counterexample());
    assert!(result.is_failure());
    assert!(!result.is_not_proved());

    let VerifyResult::Counterexample {
        model, bindings, ..
    } = &result
    else {
        panic!("expected Counterexample, got {result:?}");
    };
    assert_eq!(model.as_deref(), Some("x = -1"));
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].value, "-1");
}

#[test]
fn not_proved_and_counterexample_are_distinguishable_failures() {
    // Both are failures, but only one claims a witness. Consumers can always
    // tell which, so no counterexample narrative is ever fabricated.
    let not_proved = VerifyResult::unknown("gap", Some(UnknownCategory::Incompleteness));
    let counterexample = VerifyResult::Counterexample {
        obligation_name: "ensures".to_string(),
        model: Some("x = 0".to_string()),
        bindings: Vec::new(),
    };

    assert!(not_proved.is_failure() && counterexample.is_failure());
    assert!(not_proved.is_not_proved() && !counterexample.is_not_proved());
    assert!(counterexample.is_counterexample() && !not_proved.is_counterexample());
}
