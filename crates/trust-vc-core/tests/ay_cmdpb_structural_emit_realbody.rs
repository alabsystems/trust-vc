// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the SUBMISSION binary's structural-UNSAT VERDICT-EMISSION
// DISPATCH fixture: the MAIN `ay` CLI's PB-solve dispatch
// (`crates/ay/src/cmd_pb.rs` `solve_opb`) emits `s UNSATISFIABLE` via the early
// structural route ONLY WHEN the emit guard
// `objective.is_none() && proof.is_none() && structural_unsat_self_checked(..)`
// holds, and `structural_unsat_self_checked` is the SHORT-CIRCUIT OR of the four
// self-checked recognizers. Each soundness contract PROVES:
//   * (P1) `structural_unsat_self_checked_emit` — OR-composition: a self-check
//     implies SOME recognizer accepted (a kernel-algebra-checked refutation exists);
//   * (P2) `emit_unsat_guard` — the structural gate is load-bearing on the emit route;
//   * (COMBINED) `emit_unsat_implies_checked_refutation` — emit `s UNSATISFIABLE`
//     ==> some recognizer accepted ==> a checked refutation exists ==> UNSAT.
// Each unsound control (OR true with no recognizer / drop the structural gate) is
// REFUTED with a concrete counterexample. See the fixture header.
//
// `tests/fixtures/ay_cmdpb_structural_emit_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/cmdpb_structural_emit_realbody.rs` in the `ay`
// repo. Override with `AY_PB_CMDPB_STRUCTURAL_PROOF_SRC` to verify directly against
// an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_CMDPB_STRUCTURAL_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_cmdpb_structural_emit_realbody.rs",
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

// ── (P1) OR-COMPOSITION: structural self-check ⟹ some recognizer accepted ───────
#[test]
fn structural_unsat_self_checked_emit_verified() {
    assert_verified("structural_unsat_self_checked_emit");
}
#[test]
fn structural_unsat_self_checked_no_rec_wrong_refuted() {
    assert_counterexample("structural_unsat_self_checked_no_rec_wrong");
}

// ── (P2) EMIT GUARD LOAD-BEARING: emit route ⟹ structural gate held ─────────────
#[test]
fn emit_unsat_guard_verified() {
    assert_verified("emit_unsat_guard");
}
#[test]
fn emit_unsat_guard_no_gate_wrong_refuted() {
    assert_counterexample("emit_unsat_guard_no_gate_wrong");
}

// ── (COMBINED) emit `s UNSATISFIABLE` ⟹ a kernel-algebra-checked refutation ─────
#[test]
fn emit_unsat_implies_checked_refutation_verified() {
    assert_verified("emit_unsat_implies_checked_refutation");
}
#[test]
fn emit_unsat_no_gate_wrong_refuted() {
    assert_counterexample("emit_unsat_no_gate_wrong");
}
