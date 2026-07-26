// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the SUBMISSION binary's DECISION-SAT self-check
// (Verified-SAT-Gate, VSG) soundness fixture: the MAIN `ay` CLI's PB-solve
// emission (`crates/ay/src/cmd_pb.rs` `decision_sat_self_checked`, funneled from
// `run_solve`) emits `s SATISFIABLE` for a decision (`objective.is_none()`)
// instance ONLY WHEN the returned model RE-VERIFIES against the ORIGINAL
// `instance.constraints` with the proven `ay_pb::verify_all_constraints`. This is
// the decision-track analogue of the OPTIMIZATION incumbent VIG
// (`ay_incumbent_vig_realbody.rs`). Both PRIME DIRECTIVES are proven:
//   * (P1) `decision_sat_emit_implies_feasible` — SOUNDNESS: emit `s SATISFIABLE`
//     ⟹ the model re-verified (fail-closed, never a wrong SAT);
//   * (P2) `decision_sat_feasible_stays_satisfiable` — 0-REGRESSION: a verifying
//     model is ALWAYS still emitted SAT (no false UNKNOWN on a valid model);
//   * (COMBINED) `decision_sat_gate_decision` — emit `s SATISFIABLE` ⟺ (was_sat ∧
//     feasible), the EXACT gate decision, jointly P1 ∧ P2.
// Each soundness contract PROVES; each unsound control (drop the VSG re-check /
// over-eagerly downgrade a verifying model) is REFUTED with a concrete
// counterexample. See the fixture header for the modeling.
//
// `tests/fixtures/ay_decision_sat_vig_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/decision_sat_vig_realbody.rs` in the `ay` repo.
// Override with `AY_PB_DECISION_SAT_VIG_PROOF_SRC` to verify directly against an
// `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_DECISION_SAT_VIG_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_decision_sat_vig_realbody.rs",
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

// ── P1: SOUNDNESS — emit `s SATISFIABLE` ⟹ the model re-verified ─────────────
#[test]
fn decision_sat_emit_implies_feasible_verified() {
    assert_verified("decision_sat_emit_implies_feasible");
}
#[test]
fn decision_sat_emit_implies_feasible_no_check_wrong_refuted() {
    assert_counterexample("decision_sat_emit_implies_feasible_no_check_wrong");
}

// ── P2: 0-REGRESSION — a verifying model is never turned into a false UNKNOWN ──
#[test]
fn decision_sat_feasible_stays_satisfiable_verified() {
    assert_verified("decision_sat_feasible_stays_satisfiable");
}
#[test]
fn decision_sat_feasible_stays_satisfiable_overeager_wrong_refuted() {
    assert_counterexample("decision_sat_feasible_stays_satisfiable_overeager_wrong");
}

// ── COMBINED: emit `s SATISFIABLE` ⟺ (was_sat ∧ feasible) ─────────────────────
#[test]
fn decision_sat_gate_decision_verified() {
    assert_verified("decision_sat_gate_decision");
}
#[test]
fn decision_sat_gate_decision_no_check_wrong_refuted() {
    assert_counterexample("decision_sat_gate_decision_no_check_wrong");
}
