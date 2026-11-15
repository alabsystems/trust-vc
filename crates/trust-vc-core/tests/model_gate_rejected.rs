// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! END-TO-END probe for the THIRD Unknown category
//! ([`UnknownCategory::ModelGateRejected`]) and its controls.
//!
//! The trigger is ay defect A, `docs/ay-defect-2026-09-17-quantified-axiom-family.md`:
//! a quantified definitional axiom whose body READS THE BOUND VARIABLE with no
//! ground instance. ay publishes a model, its own independent model-check gate
//! ground-falsifies the axiom under that model, prints
//! `[AY SOUNDNESS GATE] caught an INVALID model` and fail-closes
//! `Sat -> Unknown`. Deterministic: 15/15 runs in that investigation, and
//! reproduced here on 2026-09-17 at ay `0dc8f8f0b` (the SIBLING working tree
//! the `[patch]` binds, NOT the `4cadc2bf` manifest pin).
//!
//! What this file pins:
//!   1. the probe still fails CLOSED and its verdict has not moved;
//!   2. a genuine refutation still reports as a Counterexample WITH a model;
//!   3. one ground instance removes the trigger entirely and the same spec fn
//!      then verifies — the discriminator the investigation measured;
//!   4. a RATCHET on the measured gap between ay's gate and trust-vc's seam.
//!
//! The category-level decision (gate statistics -> `ModelGateRejected`, and the
//! liar twins that must stay REFUTED) is pinned at the seam in
//! `encoder::verification::unknown_category::tests`, because `SolveDetails` is
//! `#[non_exhaustive]` and cannot be constructed from an integration test.

use trust_vc_core::{verify_function_from_file, UnknownCategory, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/model_gate_rejected.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

/// The probe fails CLOSED. Whatever category it is attributed to, it must never
/// become `Verified` — the goal is valid, trust-vc cannot discharge it, and
/// claiming otherwise would be a false Verified.
#[test]
fn gate_probe_fails_closed() {
    let result = verdict("t_gate_rejected");
    assert!(
        !result.is_verified(),
        "UNSOUND: the model-gate probe must never verify, got {result:?}"
    );
    assert!(
        result.is_failure(),
        "the obligation was not discharged and must be reported as a failure, got {result:?}"
    );
    assert!(
        !result.is_counterexample(),
        "no model may be attached: nothing refuted the obligation, got {result:?}"
    );
}

/// CONTROL 1 — a genuine refutation is still a `Counterexample` WITH a model.
/// If this ever became `NotProved`, the reporting change would have eaten real
/// counterexamples.
#[test]
fn control_a_genuine_refutation_still_reports_a_counterexample_with_a_model() {
    let result = verdict("c_real_counterexample");
    match &result {
        VerifyResult::Counterexample { model, .. } => {
            assert!(
                model.as_deref().is_some_and(|m| m.contains('3')),
                "a real refutation must still carry its witness, got {model:?}"
            );
        }
        other => panic!("a genuine refutation must stay a Counterexample, got {other:?}"),
    }
    assert!(result.is_counterexample());
    assert_eq!(
        result.unknown_category(),
        None,
        "a real counterexample carries no unknown category"
    );
}

/// CONTROL 2 — the DISCRIMINATOR. The same binder-reading spec fn, plus one
/// ground instance for the instantiation lane to fire on, verifies and triggers
/// no gate at all. This is what makes the probe a probe: if this ever goes red,
/// the fixture stopped isolating the trigger.
#[test]
fn control_a_ground_instance_removes_the_trigger() {
    let result = verdict("p_ground");
    assert!(
        result.is_verified(),
        "one ground instance must remove the trigger and verify, got {result:?}"
    );
}

/// The probe's VERDICT has not moved. This change relabels a category; it must
/// not reclassify the outcome. `NotProved` is the model-less failure variant
/// both `Incompleteness` and `ModelGateRejected` route to, so either category
/// is acceptable here — what is NOT acceptable is a soft `Unknown` (which would
/// have turned a failure into a non-failure) or a `Counterexample` with an
/// invented model.
#[test]
fn gate_probe_verdict_did_not_move() {
    let result = verdict("t_gate_rejected");
    assert!(
        matches!(result, VerifyResult::NotProved { .. }),
        "the probe must stay on the model-less failure variant, got {result:?}"
    );
    let category = result
        .unknown_category()
        .expect("NotProved always carries the category that justified it");
    assert!(
        matches!(
            category,
            UnknownCategory::Incompleteness | UnknownCategory::ModelGateRejected
        ),
        "the probe must stay in the incompleteness-routing class, got {category:?}"
    );
    assert!(
        category.is_incompleteness(),
        "the routing predicate must hold, got {category:?}"
    );
}

/// RATCHET on a MEASURED GAP — read this before "fixing" it.
///
/// Measured 2026-09-17 at ay `0dc8f8f0b`, with temporary instrumentation on
/// every `check_sat_with_details` return: for THIS trigger ay's gate keys never
/// reach trust-vc. The probe's two solve envelopes carry
/// `unknown.phase = "quantifier-instantiation"` and NO
/// `model_check_gate.result`; across a whole `evals/verus/ported/choose.rs` run
/// (96 solves, 54 banners) `model_check_gate.result` arrived 14 times and every
/// single one was `confirmed-sat` — the gate ACCEPTING a model. The 3 banners
/// this probe prints come from ay-INTERNAL sub-solves whose statistics are
/// restored away before the outer envelope is built.
///
/// So the report that prompted this work is WRONG on exactly one point: ay does
/// NOT today hand trust-vc the attribution on the envelope it returns. The
/// consumer half is nevertheless implemented, correct, and pinned at the seam;
/// it goes live the moment ay preserves the keys.
///
/// THIS TEST ASSERTS THE GAP, so that the day it closes we are told. If it
/// fails with `ModelGateRejected`, ay has started preserving the attribution:
/// that is GOOD NEWS — delete this test and tighten
/// `gate_probe_verdict_did_not_move` to require `ModelGateRejected` exactly.
/// Do NOT "fix" it by loosening the seam detector.
#[test]
fn ratchet_ay_gate_keys_do_not_yet_reach_the_solve_envelope() {
    let category = verdict("t_gate_rejected")
        .unknown_category()
        .expect("the probe is always an incompleteness-class failure");
    assert_eq!(
        category,
        UnknownCategory::Incompleteness,
        "RATCHET: expected the measured 2026-09-17 state (ay's gate attribution \
         does not survive to `check_sat_with_details`, so the probe is still \
         classified as a plain incompleteness). Got {category:?}. If this is \
         ModelGateRejected, ay now preserves the keys — delete this ratchet and \
         tighten `gate_probe_verdict_did_not_move`."
    );
}
