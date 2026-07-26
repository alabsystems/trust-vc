// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb cutting-planes SATURATION step soundness
// fixture: `impliedGe_saturate` (refutation_check.rs:167-179) — capping each
// coefficient at the degree `b` (`c.min(self.rhs)`) under the side conditions
// `a_i >= 0`, `b >= 0` — is entailment-preserving over 0/1 points (matches the
// kernel arrow `ay_certcut_saturation_sound`). This is the rule the cutting-planes
// checker-proof `wo0h78ivd` explicitly left uncovered. Each soundness contract
// PROVES; each deliberately-unsound (over-capping / relation-dropping /
// over-claiming) control is REFUTED. See the fixture header for the loop-invariant
// decomposition and the `int`(ℤ)/checked-overflow modeling.
//
// `tests/fixtures/ay_saturate_step_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/saturate_step_realbody.rs` in the `ay` repo.
// Override with `AY_PB_SATURATE_PROOF_SRC` to verify directly against an `ay`
// checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_SATURATE_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_saturate_step_realbody.rs",
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

// ── PIECE 1: the per-coefficient cap c.min(self.rhs) ─────────────────────────
#[test]
fn saturate_cap_verified() {
    assert_verified("saturate_cap");
}
#[test]
fn saturate_cap_overcap_wrong_refuted() {
    assert_counterexample("saturate_cap_overcap_wrong");
}

// ── PIECE 1b: the per-term loop body at a 0/1 point ──────────────────────────
#[test]
fn saturate_term_contrib_verified() {
    assert_verified("saturate_term_contrib");
}
#[test]
fn saturate_term_contrib_overcap_wrong_refuted() {
    assert_counterexample("saturate_term_contrib_overcap_wrong");
}

// ── PIECE 2: the CRUX inductive step of the loop invariant ───────────────────
#[test]
fn saturate_invariant_step_verified() {
    assert_verified("saturate_invariant_step");
}
#[test]
fn saturate_invariant_step_no_relation_wrong_refuted() {
    // The per-term cap relation `s_term == o || s_term == b` is load-bearing:
    // dropping it makes the invariant step unsound, so it is REFUTED.
    assert_counterexample("saturate_invariant_step_no_relation_wrong");
}

// ── PIECE 3: invariant ⟹ soundness ──────────────────────────────────────────
#[test]
fn saturate_invariant_implies_sound_verified() {
    assert_verified("saturate_invariant_implies_sound");
}
#[test]
fn saturate_invariant_overclaim_wrong_refuted() {
    assert_counterexample("saturate_invariant_overclaim_wrong");
}

// ── CONCRETE WITNESS: single-coefficient saturation soundness end-to-end ─────
#[test]
fn saturate_single_term_sound_verified() {
    assert_verified("saturate_single_term_sound");
}
#[test]
fn saturate_single_term_overcap_wrong_refuted() {
    assert_counterexample("saturate_single_term_overcap_wrong");
}
