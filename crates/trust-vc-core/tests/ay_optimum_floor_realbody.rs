// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb cutting-planes OPTIMUM self-check soundness
// fixture: a floor `check_floor` accepts is a TRUE lower bound on the objective
// over the feasible region (the `derived == target` transport), the
// `var_geq_zero` lift is sound, and the `certify_optimum` tightness gate fires
// only at `F == UB`. Each soundness contract PROVES; each unsound control is
// REFUTED or does not verify. See the fixture header for scope/modeling.
//
// `tests/fixtures/ay_optimum_floor_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/optimum_floor_realbody.rs` in the `ay` repo.
// Override with `AY_PB_OPTIMUM_PROOF_SRC` to verify against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_OPTIMUM_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_optimum_floor_realbody.rs",
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

// ── check_floor terminal: derived==target transports the floor to the objective ─
#[test]
fn check_floor_terminal_sound_verified() {
    assert_verified("check_floor_terminal_sound");
}
#[test]
fn check_floor_wrong_form_refuted() {
    assert_counterexample("check_floor_wrong_form");
}
#[test]
fn check_floor_overcount_wrong_refuted() {
    assert_counterexample("check_floor_overcount_wrong");
}

// ── var_geq_zero LIFT soundness ──────────────────────────────────────────────
#[test]
fn lift_var_geq_zero_sound_verified() {
    assert_verified("lift_var_geq_zero_sound");
}
#[test]
fn lift_var_geq_zero_no_lemma_verified() {
    // Re-keyed to verified (docs/execution-plan §7 2026-07-19): a product of
    // non-negatives is non-negative — a TRUE fact ay's improved NIA (pin 5665ac65)
    // derives unaided, so the explicit lemma is no longer load-bearing. The stale
    // "no-lemma-not-verified" control was a completeness gap, not a soundness hole
    // (mutation-verified sound: sign-drop mutants refute).
    assert_verified("lift_var_geq_zero_no_lemma");
}

// ── certify_optimum tightness gate (LB == UB) ────────────────────────────────
#[test]
fn certify_optimum_tightness_sound_verified() {
    assert_verified("certify_optimum_tightness_sound");
}
#[test]
fn certify_optimum_drop_tightness_refuted() {
    assert_counterexample("certify_optimum_drop_tightness");
}
