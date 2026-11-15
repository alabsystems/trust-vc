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

/// A confirmation failure that QUOTES the re-solve's own timeout reason is
/// still a `ConfirmationDisagree`, never a `Timeout`.
///
/// Both confirmation sites now print what the re-solve actually returned, so
/// this recovery classifier sees reason strings that contain another
/// category's trigger phrase. The generated marker has to win: `Timeout` is
/// the retriable category, and a confirmation failure that is re-read as a
/// retriable timeout would be re-attempted instead of reported.
#[test]
fn confirmation_marker_beats_a_quoted_timeout_reason() {
    let reason = "Confirmation check disagreed for 'assertion_2': the re-solve returned \
                  Unknown/Timeout (Solver returned unknown (timeout) for 'assertion_2') \
                  — fail-closed";
    assert_eq!(
        UnknownCategory::classify(reason),
        UnknownCategory::ConfirmationDisagree
    );
    let inductive = "Confirmation check disagreed for 'inv' (inductive step): the re-solve \
                     returned Unknown { reason: \"Solver returned unknown (timeout) for \
                     'inv'\", category: Some(Timeout), detail: None } — fail-closed";
    assert_eq!(
        UnknownCategory::classify(inductive),
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
        location: None,
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
        location: None,
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
        location: None,
        model: Some("x = 0".to_string()),
        bindings: Vec::new(),
    };

    assert!(not_proved.is_failure() && counterexample.is_failure());
    assert!(not_proved.is_not_proved() && !counterexample.is_not_proved());
    assert!(counterexample.is_counterexample() && !not_proved.is_counterexample());
}

// ───────────────────── THE THIRD CATEGORY: ModelGateRejected ─────────────────
//
// ay's independent model-check gate refuting ay's OWN model is neither a
// refutation of the user's proof nor a resource limit. Pinned here at the seam
// that decides it, against a REAL `ay_dpll::Statistics` carrying ay's real key
// names — `SolveDetails` is `#[non_exhaustive]` and cannot be built here, but
// `Statistics` is `Default` with a public `set_string`, so the key strings
// under test are the ones ay actually writes.
//
// Source of the key names: `ay-dpll/src/executor/model/independent_gate.rs`
// (`downgrade_sat_after_gate` sets `unknown.phase`; the `ModelViolates` arm
// sets `model_check_gate.result`/`.violated_assertion`). Measured at ay
// `0dc8f8f0b` (the SIBLING working tree the `[patch]` binds, not the
// `4cadc2bf` manifest pin). See
// `docs/ay-defect-2026-09-17-quantified-axiom-family.md`.

use crate::encoder::verification::solve::{
    model_gate_rejection_from_stats, render_model_gate_rejection, solver_unknown_outcome,
    AY_MODEL_GATE_PHASE, AY_MODEL_GATE_VIOLATES,
};
use ay_dpll::{Statistics, UnknownReason};

/// The statistics ay writes on the `ModelViolates` downgrade.
fn gate_violated_stats() -> Statistics {
    let mut s = Statistics::default();
    s.set_string("unknown.reason", "incomplete");
    s.set_string("unknown.phase", AY_MODEL_GATE_PHASE);
    s.set_string(
        "unknown.detail",
        "model-not-independently-confirmed: an assertion is falsified by the model",
    );
    s.set_string("model_check_gate.result", AY_MODEL_GATE_VIOLATES);
    s.set_string(
        "model_check_gate.violated_assertion",
        "(forall ((__trust_vc_spec_g_i Int)) (= (g __trust_vc_spec_g_i) (<= 5 __trust_vc_spec_g_i)))",
    );
    s
}

#[test]
fn gate_rejection_is_detected_and_names_the_violated_assertion() {
    let stats = gate_violated_stats();
    let gate = model_gate_rejection_from_stats(&stats, None)
        .expect("ay's ModelViolates statistics must be recognized as a gate rejection");
    assert!(
        gate.violated_assertion
            .as_deref()
            .is_some_and(|t| t.contains("__trust_vc_spec_g_i")),
        "the gate rejection must carry ay's own violated assertion, got {:?}",
        gate.violated_assertion
    );
}

#[test]
fn gate_rejection_is_detected_from_the_typed_phase_alone() {
    // `SolveDetails::unknown_diagnostic.phase` is the same `unknown.phase`
    // string, typed (ay `api/solving/controls.rs::build_unknown_diagnostic`).
    // Either channel alone is sufficient evidence.
    let empty = Statistics::default();
    assert!(
        model_gate_rejection_from_stats(&empty, Some(AY_MODEL_GATE_PHASE)).is_some(),
        "the typed phase alone must be sufficient evidence"
    );
}

// ── LIAR TWINS: every near-miss must be REFUTED, not absorbed ──

#[test]
fn liar_twin_plain_incompleteness_is_not_a_gate_rejection() {
    // THE TWIN THAT MATTERS. This is the exact envelope trust-vc sees today on
    // the `m_ge5` probe (measured 2026-09-17): `UnknownReason` is a quantifier
    // incompleteness and `unknown.phase` is "quantifier-instantiation", with NO
    // gate keys. It must stay `Incompleteness` — if this seam ever promoted a
    // plain incompleteness to the third category, the fix would be laundering
    // real incompleteness as an ay defect.
    let mut s = Statistics::default();
    s.set_string("unknown.phase", "quantifier-instantiation");
    s.set_string(
        "unknown.detail",
        "E-matching touched existential quantifiers in an incomplete mode",
    );
    assert!(
        model_gate_rejection_from_stats(&s, Some("quantifier-instantiation")).is_none(),
        "a quantifier-instantiation unknown is NOT a caught invalid model"
    );

    let outcome = solver_unknown_outcome(
        "assertion_0",
        Some("m_ge5.rs:7:5"),
        Some(UnknownReason::QuantifierEmatchingExistsIncomplete),
        None,
    );
    let result = outcome_to_verify_result(outcome);
    assert_eq!(
        result.unknown_category(),
        Some(UnknownCategory::Incompleteness),
        "no gate evidence must leave the category at Incompleteness, got {result:?}"
    );
}

#[test]
fn liar_twin_confirmed_sat_is_not_a_gate_rejection() {
    // `confirmed-sat` is the gate ACCEPTING a model — the opposite outcome. It
    // is the only `model_check_gate.result` value measured reaching trust-vc on
    // 2026-09-17 (14 times in one `choose.rs` run), so mistaking it for a
    // rejection would misreport real, healthy solves.
    let mut s = Statistics::default();
    s.set_string("model_check_gate.result", "confirmed-sat");
    assert!(model_gate_rejection_from_stats(&s, None).is_none());
}

#[test]
fn liar_twin_cannot_confirm_is_not_a_gate_rejection() {
    // `cannot-confirm` is a COVERAGE GAP — the gate could not decide — not
    // evidence that ay's model is false. ay's own comment insists on the
    // distinction; so does this seam.
    let mut s = Statistics::default();
    s.set_string("model_check_gate.result", "cannot-confirm");
    s.set_string(
        "model_check_gate.cannot_confirm_reason",
        "SmtCircularSatFallback",
    );
    assert!(model_gate_rejection_from_stats(&s, None).is_none());
}

#[test]
fn liar_twin_empty_statistics_is_not_a_gate_rejection() {
    assert!(model_gate_rejection_from_stats(&Statistics::default(), None).is_none());
}

// ── the reporting change itself ──

fn outcome_to_verify_result(
    outcome: crate::encoder::verification::outcome::AssertionOutcome,
) -> VerifyResult {
    match outcome {
        crate::encoder::verification::outcome::AssertionOutcome::Unknown {
            reason,
            category,
            ..
        } => VerifyResult::unknown(reason, category),
        other => panic!("expected an Unknown outcome, got {other:?}"),
    }
}

#[test]
fn gate_rejection_classifies_as_the_third_category_and_not_incompleteness() {
    let stats = gate_violated_stats();
    let gate = model_gate_rejection_from_stats(&stats, None).expect("gate rejection");
    // ay sets `UnknownReason::Incomplete` on this downgrade, which the
    // reason-code mapping alone would call `Incompleteness`. The gate
    // attribution is the more specific fact and must win.
    let outcome = solver_unknown_outcome(
        "assertion_0",
        Some("m_ge5.rs:7:5"),
        Some(UnknownReason::Incomplete),
        Some(&gate),
    );
    let result = outcome_to_verify_result(outcome);
    assert_eq!(
        result.unknown_category(),
        Some(UnknownCategory::ModelGateRejected),
        "a caught invalid model must be its OWN category, got {result:?}"
    );
    assert_ne!(
        result.unknown_category(),
        Some(UnknownCategory::Incompleteness),
        "the third category must not be absorbed by Incompleteness"
    );
}

#[test]
fn gate_rejection_does_not_move_the_verdict_and_still_fails_closed() {
    // THE WHOLE POINT: this is a REPORTING fix. The obligation still is not
    // discharged, still fails closed, and still lands on exactly the same
    // `VerifyResult` variant a plain incompleteness lands on — so no corpus
    // verdict can move.
    let stats = gate_violated_stats();
    let gate = model_gate_rejection_from_stats(&stats, None).expect("gate rejection");
    let gated = outcome_to_verify_result(solver_unknown_outcome(
        "assertion_0",
        None,
        Some(UnknownReason::Incomplete),
        Some(&gate),
    ));
    let plain = outcome_to_verify_result(solver_unknown_outcome(
        "assertion_0",
        None,
        Some(UnknownReason::Incomplete),
        None,
    ));
    // Named oracles (house rule, pinned by
    // `encoder::tests::result_oracles::test_targeted_verification_tests_use_named_oracles`):
    // these also assert the routing invariant — `NotProved` must carry an
    // incompleteness-class category — which is exactly the property that keeps
    // this relabel verdict-preserving.
    crate::encoder::tests::result_oracles::expect_incompleteness_modelless_failure(
        &gated,
        "a caught invalid model",
    );
    crate::encoder::tests::result_oracles::expect_incompleteness_modelless_failure(
        &plain,
        "a plain incompleteness",
    );
    assert!(!gated.is_verified(), "must never become Verified");
    assert!(gated.is_failure(), "must still fail closed");
    assert!(
        !gated.is_counterexample(),
        "no model may be attached: nothing refuted the obligation"
    );
    assert!(
        UnknownCategory::ModelGateRejected.is_incompleteness(),
        "the shared routing predicate is what keeps the verdict identical"
    );
}

#[test]
fn gate_rejection_message_does_not_say_the_proof_is_wrong() {
    let stats = gate_violated_stats();
    let gate = model_gate_rejection_from_stats(&stats, None).expect("gate rejection");
    let rendered = render_model_gate_rejection(&gate);
    assert!(
        rendered.contains("NOT a refutation"),
        "the message must deny that this refutes the proof, got: {rendered}"
    );
    assert!(
        rendered.contains("could not independently confirm")
            || rendered.contains("refuted the model ay"),
        "the message must say what actually happened, got: {rendered}"
    );
    assert!(
        rendered.contains("__trust_vc_spec_g_i"),
        "the message must name the assertion ay falsified, got: {rendered}"
    );
    let suggestion = UnknownCategory::ModelGateRejected.actionable_suggestion();
    assert!(
        suggestion.contains("Not a refutation of your proof"),
        "the suggestion must not blame the proof, got: {suggestion}"
    );
    assert!(
        !suggestion.contains("supply an explicit proof"),
        "the incompleteness remedy is the WRONG advice here, got: {suggestion}"
    );
    assert_ne!(
        suggestion,
        UnknownCategory::Incompleteness.actionable_suggestion(),
        "the two categories must not read alike"
    );
}

#[test]
fn gate_rejection_is_soundness_relevant_and_not_retriable() {
    let c = UnknownCategory::ModelGateRejected;
    assert!(
        c.is_soundness_relevant(),
        "a solver that refuted its own model has a defect worth counting"
    );
    assert!(
        c.is_solver_limitation(),
        "the defect is ay-side, not a trust-vc bug"
    );
    assert!(
        !c.is_retriable(),
        "deterministic in 15/15 runs measured 2026-09-17: a retry buys nothing"
    );
}

#[test]
fn gate_evidence_can_never_promote_a_resource_unknown_into_a_failure() {
    // THE SOUNDNESS-BOUNDARY CONTROL for this change. A resource/timeout
    // `Unknown` must stay a NON-failure `Unknown` even when ay's gate keys are
    // present on the same envelope — otherwise a "reporting fix" would have
    // moved a verdict across the exact boundary
    // `design-unknown-as-failure.md` draws.
    let stats = gate_violated_stats();
    let gate = model_gate_rejection_from_stats(&stats, None).expect("gate rejection");
    for reason in [
        UnknownReason::Timeout,
        UnknownReason::ResourceLimit,
        UnknownReason::MemoryLimit,
        UnknownReason::Interrupted,
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
        UnknownReason::SplitLimit,
    ] {
        let with_gate = outcome_to_verify_result(solver_unknown_outcome(
            "assertion_0",
            None,
            Some(reason),
            Some(&gate),
        ));
        let without_gate = outcome_to_verify_result(solver_unknown_outcome(
            "assertion_0",
            None,
            Some(reason),
            None,
        ));
        crate::encoder::tests::result_oracles::expect_resource_unknown_not_failure(
            &with_gate,
            &format!("{reason:?} with gate evidence"),
        );
        assert!(
            !with_gate.is_failure(),
            "{reason:?} must never become a failure, got {with_gate:?}"
        );
        assert_eq!(
            with_gate.unknown_category(),
            without_gate.unknown_category(),
            "{reason:?}: gate evidence must not change a RESOURCE category"
        );
        assert_ne!(
            with_gate.unknown_category(),
            Some(UnknownCategory::ModelGateRejected),
            "{reason:?} must not be relabelled into the third category"
        );
    }
}

#[test]
fn the_relabel_is_verdict_preserving_over_every_category() {
    // Exhaustive proof-by-construction of "no verdict moves": for EVERY
    // category, relabelling with gate evidence leaves `is_incompleteness()` —
    // the single predicate `VerifyResult::unknown` routes on — unchanged.
    use crate::encoder::verification::solve::gate_relabelled_category;
    for base in [
        UnknownCategory::Timeout,
        UnknownCategory::SolverPanic,
        UnknownCategory::ThreadPanic,
        UnknownCategory::ConfirmationDisagree,
        UnknownCategory::ModelNotValidated,
        UnknownCategory::EmptyModel,
        UnknownCategory::SolverUnknown,
        UnknownCategory::Incompleteness,
        UnknownCategory::ModelGateRejected,
        UnknownCategory::EncodingDemotion,
        UnknownCategory::OpaqueTypes,
        UnknownCategory::VacuousTruth,
        UnknownCategory::UnsupportedMode,
        UnknownCategory::Other,
    ] {
        let relabelled = gate_relabelled_category(base, true);
        assert_eq!(
            relabelled.is_incompleteness(),
            base.is_incompleteness(),
            "relabelling {base:?} changed the verdict-routing predicate"
        );
        assert_eq!(
            gate_relabelled_category(base, false),
            base,
            "with no gate evidence {base:?} must pass through untouched"
        );
    }
}
