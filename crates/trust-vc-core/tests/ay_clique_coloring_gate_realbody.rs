// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb IHALAINEN PBO-CLIQUE-COLORING certified-optimum
// accept-decision fixture: `clique_coloring::try_solve` (clique_coloring.rs:
// 308-360) emits `OptimumFound { value }` ONLY WHEN (1) the EXACT structural
// recognizer matched the canonical family (`detect`, under which the kernel clique
// LB theorem `opt >= n - t` applies), (2) the constructed colouring re-verified
// feasible (`verify_all_constraints`, the UB `opt <= value`), and (3) the
// tightness gate held (`value == (n - t).max(0)`). The bracket forces
// `opt == value`. Each soundness contract PROVES; each unsound control (drop the
// recognizer / feasibility / tightness re-check, or the LB premise) is REFUTED.
// See the fixture header.
//
// `tests/fixtures/ay_clique_coloring_gate_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/clique_coloring_gate_realbody.rs` in the `ay` repo.
// Override with `AY_PB_CLIQUE_COLORING_PROOF_SRC` to verify directly against an
// `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_CLIQUE_COLORING_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_clique_coloring_gate_realbody.rs",
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

// ── THE GATE: emit OPTIMUM ⟹ (recognizer ∧ feasibility re-check ∧ tight) ────────
#[test]
fn clique_coloring_emit_optimum_verified() {
    assert_verified("clique_coloring_emit_optimum");
}
#[test]
fn clique_coloring_emit_drop_recognizer_wrong_refuted() {
    assert_counterexample("clique_coloring_emit_drop_recognizer_wrong");
}
#[test]
fn clique_coloring_emit_drop_feasible_wrong_refuted() {
    assert_counterexample("clique_coloring_emit_drop_feasible_wrong");
}
#[test]
fn clique_coloring_emit_drop_tightness_wrong_refuted() {
    assert_counterexample("clique_coloring_emit_drop_tightness_wrong");
}

// ── THE CLAMP: lower_bound = (n - t).max(0) is a valid LB floor ─────────────────
#[test]
fn clique_coloring_lower_bound_verified() {
    assert_verified("clique_coloring_lower_bound");
}

// ── SOUNDNESS COROLLARY: lb <= opt <= value with value == lb forces opt == value ─
#[test]
fn clique_coloring_bracket_forces_optimum_verified() {
    assert_verified("clique_coloring_bracket_forces_optimum");
}
#[test]
fn clique_coloring_bracket_drop_lb_wrong_refuted() {
    assert_counterexample("clique_coloring_bracket_drop_lb_wrong");
}
