// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb MINIMUM DOMINATING SET certified-optimum
// accept-decision fixture: `dominating_set::try_solve` (dominating_set.rs:163-229)
// emits `OptimumFound { value }` ONLY WHEN (1) the 2-packing certificate re-check
// passed (`certified_two_packing_size`, the LB witness `|S| <= gamma`), (2) the
// chosen dominating set re-verified feasible (`verify_all_constraints`, the UB
// witness `gamma <= value`), and (3) the tightness gate held (`value ==
// packing_size`). The bracket `|S| <= gamma <= |D|` with equality forces
// `gamma == value`. Each soundness contract PROVES; each unsound control (drop the
// 2-packing / feasibility / tightness re-check) is REFUTED. See the fixture header.
//
// `tests/fixtures/ay_domset_gate_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/domset_gate_realbody.rs` in the `ay` repo.
// Override with `AY_PB_DOMSET_PROOF_SRC` to verify directly against an `ay`
// checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_DOMSET_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_domset_gate_realbody.rs",
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

// ── THE GATE: emit OPTIMUM ⟹ (packing re-check ∧ feasibility re-check ∧ tight) ──
#[test]
fn domset_emit_optimum_verified() {
    assert_verified("domset_emit_optimum");
}
#[test]
fn domset_emit_drop_packing_check_wrong_refuted() {
    assert_counterexample("domset_emit_drop_packing_check_wrong");
}
#[test]
fn domset_emit_drop_feasible_check_wrong_refuted() {
    assert_counterexample("domset_emit_drop_feasible_check_wrong");
}
#[test]
fn domset_emit_drop_tightness_wrong_refuted() {
    assert_counterexample("domset_emit_drop_tightness_wrong");
}

// ── SOUNDNESS COROLLARY: the bracket |S| <= gamma <= |D| with equality forces opt ─
#[test]
fn domset_bracket_forces_optimum_verified() {
    assert_verified("domset_bracket_forces_optimum");
}
#[test]
fn domset_bracket_drop_lower_wrong_refuted() {
    assert_counterexample("domset_bracket_drop_lower_wrong");
}
