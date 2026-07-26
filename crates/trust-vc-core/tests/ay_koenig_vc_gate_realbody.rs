// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb KÖNIG BIPARTITE MINIMUM-VERTEX-COVER
// certified-optimum accept-decision fixture: `bipartite_vertex_cover::try_solve`
// (bipartite_vertex_cover.rs:134-229) emits `OptimumFound { value }` ONLY WHEN
// (1) the cover re-verified feasible against the ORIGINAL rows
// (`verify_all_constraints`, the UB witness `tau <= value`), (2) the matching
// certificate re-check passed (`certified_matching_size`, the LB witness
// `|M| <= tau`), and (3) the tightness gate held (`value == matching_size`). The
// bracket `|M| <= tau <= |C|` with equality forces `tau == value` (König:
// max matching == min vertex cover). This is the ORIGINAL structural optimum cert
// the score levers mirror. Each soundness contract PROVES; each unsound control
// (drop the feasibility / matching / tightness re-check) is REFUTED. See the
// fixture header.
//
// `tests/fixtures/ay_koenig_vc_gate_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/koenig_vc_gate_realbody.rs` in the `ay` repo.
// Override with `AY_PB_KOENIG_PROOF_SRC` to verify directly against an `ay`
// checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_KOENIG_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_koenig_vc_gate_realbody.rs",
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

// ── THE GATE: emit OPTIMUM ⟹ (feasibility re-check ∧ matching re-check ∧ tight) ──
#[test]
fn koenig_emit_optimum_verified() {
    assert_verified("koenig_emit_optimum");
}
#[test]
fn koenig_emit_drop_feasible_check_wrong_refuted() {
    assert_counterexample("koenig_emit_drop_feasible_check_wrong");
}
#[test]
fn koenig_emit_drop_matching_check_wrong_refuted() {
    assert_counterexample("koenig_emit_drop_matching_check_wrong");
}
#[test]
fn koenig_emit_drop_tightness_wrong_refuted() {
    assert_counterexample("koenig_emit_drop_tightness_wrong");
}

// ── SOUNDNESS COROLLARY: the bracket |M| <= tau <= |C| with equality forces opt ──
#[test]
fn koenig_bracket_forces_optimum_verified() {
    assert_verified("koenig_bracket_forces_optimum");
}
#[test]
fn koenig_bracket_drop_lower_wrong_refuted() {
    assert_counterexample("koenig_bracket_drop_lower_wrong");
}
