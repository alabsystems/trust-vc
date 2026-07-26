// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb cutting-planes REFUTATION self-check soundness
// fixture: every derivation step `refutation_check::replay_derivation` accepts is
// an entailment-preserving rule (impliedGe_add/scale/division + rhs weakening),
// and the terminal `0 >= c (c>=1)` is genuinely unsatisfiable. Each soundness
// contract PROVES; each deliberately-unsound control is REFUTED or does not
// verify. See the fixture header for the per-step vs whole-loop scope and the
// `int`(ℤ)/checked-overflow modeling.
//
// `tests/fixtures/ay_refutation_step_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/refutation_step_realbody.rs` in the `ay` repo.
// Override with `AY_PB_PROOF_SRC` to verify directly against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_REFUTATION_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_refutation_step_realbody.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

fn assert_verified(name: &str) {
    let v = verify(name);
    assert!(
        matches!(v, VerifyResult::Verified),
        "{name} must PROVE its soundness contract; got {v:?}"
    );
}

fn assert_counterexample(name: &str) {
    let v = verify(name);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "{name} (unsound control) MUST be refuted with a counterexample; got {v:?}"
    );
}

/// Unknown-as-failure relaxation (docs/design-unknown-as-failure.md): a genuine
/// verification FAILURE — a model-bearing `Counterexample` OR a model-less
/// `NotProved` (an incompleteness fail-close under the ay bump's wrong-SAT
/// closures). For unsound controls whose refutation must be a decisive failure
/// (never a soft `Unknown`), without demanding a fabricated model.
fn assert_fails(name: &str) {
    let v = verify(name);
    assert!(
        v.is_failure(),
        "{name} (unsound control) MUST be refuted — Counterexample or NotProved; got {v:?}"
    );
}

// ── RULE 1: ADD (impliedGe_add) ──────────────────────────────────────────────
#[test]
fn add_step_sound_verified() {
    assert_verified("add_step_sound");
}
#[test]
fn add_step_overclaim_refuted() {
    assert_counterexample("add_step_overclaim");
}

// ── RULE 2: SCALE (impliedGe_scale) ──────────────────────────────────────────
#[test]
fn scale_step_sound_general_verified() {
    assert_verified("scale_step_sound_general");
}
#[test]
fn scale_step_no_lemma_verified() {
    // Re-keyed to verified (docs/execution-plan §7 2026-07-19): the monotonicity
    // fact `k>=1 & a>=b ⟹ k*a>=k*b` is TRUE, and ay's improved NIA (pin 5665ac65)
    // derives it unaided — the explicit lemma is no longer load-bearing. The stale
    // "no-lemma-not-verified" control was a completeness gap, not a soundness hole
    // (mutation-verified sound: sign-drop mutants refute).
    assert_verified("scale_step_no_lemma");
}
#[test]
fn scale_step_by2_sound_verified() {
    assert_verified("scale_step_by2_sound");
}
#[test]
fn scale_step_by2_overclaim_refuted() {
    assert_counterexample("scale_step_by2_overclaim");
}

// ── RULE 3: DIVIDE (impliedGe_division), ceiling rounds up ───────────────────
#[test]
fn ceil_div_by2_rounds_up_verified() {
    // The REAL ceil_div algorithm (div_euclid/rem_euclid + `if r==0`) over ℤ at
    // the representative divisor 2, via the new div_euclid-on-int capability.
    assert_verified("ceil_div_by2_rounds_up");
}
#[test]
fn floor_div_by2_wrong_refuted() {
    assert_counterexample("floor_div_by2_wrong");
}
#[test]
fn ceil_div_general_rem_pos_verified() {
    assert_verified("ceil_div_general_rem_pos");
}
#[test]
fn ceil_div_general_rem_zero_verified() {
    assert_verified("ceil_div_general_rem_zero");
}
#[test]
fn floor_div_general_wrong_refuted() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): this wrong-body
    // refutation now fail-closes to a model-less NotProved — still a failure.
    assert_fails("floor_div_general_wrong");
}

// ── RULE 4: WEAKEN (rhs order) ───────────────────────────────────────────────
#[test]
fn weaken_step_sound_verified() {
    assert_verified("weaken_step_sound");
}

// ── TERMINAL: contradiction (pb_unsat_of_contradictory_bounds) ───────────────
#[test]
fn contradiction_terminal_unsat_verified() {
    assert_verified("contradiction_terminal_unsat");
}
#[test]
fn contradiction_terminal_wrong_refuted() {
    assert_counterexample("contradiction_terminal_wrong");
}
