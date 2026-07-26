// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb GF(2)-PARITY UNSAT accept-decision fixture for
// the `EC_ODD_GRIDS` (handshake-lemma) family (gf2_parity.rs). Two shipped arms:
//
//   ARM A (PRIMARY, kernel-CHECKED): `gf2_parity_unsat_cp_checked`
//   (gf2_parity.rs:1116-1118, ay.rs:778-779) returns `true` ONLY WHEN the parity
//   refutation, reconstructed as cutting planes over the ORIGINAL equality rows, is
//   CERTIFIED by `Refutation::check` (the `?` at gf2_parity.rs:1101) — like
//   pigeonhole routes UNSAT through `Refutation::check`.
//
//   ARM B (RECOVERY, raw elimination): `gf2_parity_detects_unsat`
//   (gf2_parity.rs:203-248, via `_with_recovery` at ay.rs:807-808) returns `true`
//   ONLY WHEN some row is the inconsistent `0 == 1` GF(2) row: odd RHS parity
//   (`aug`) AND empty variable support.
//
// Each soundness contract PROVES; each unsound control (drop the checker gate / the
// empty-support test / the odd-RHS test / the existence of a contradictory row) is
// REFUTED. See the fixture header.
//
// `tests/fixtures/ay_gf2_parity_gate_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/gf2_parity_gate_realbody.rs` in the `ay` repo.
// Override with `AY_PB_GF2_PROOF_SRC` to verify directly against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_GF2_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_gf2_parity_gate_realbody.rs",
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

// ── ARM A: emit UNSAT ⟹ Refutation::check accepted the reconstructed derivation ──
#[test]
fn gf2_cp_refutation_emit_some_verified() {
    assert_verified("gf2_cp_refutation_emit_some");
}
#[test]
fn gf2_cp_refutation_emit_some_no_check_wrong_refuted() {
    assert_counterexample("gf2_cp_refutation_emit_some_no_check_wrong");
}
#[test]
fn gf2_unsat_cp_checked_emitted_verified() {
    assert_verified("gf2_unsat_cp_checked_emitted");
}

// ── ARM B: per-row `0 == 1` predicate (odd RHS ∧ empty support) ──────────────────
#[test]
fn gf2_row_is_contradiction_verified() {
    assert_verified("gf2_row_is_contradiction");
}
#[test]
fn gf2_row_drop_support_check_wrong_refuted() {
    assert_counterexample("gf2_row_drop_support_check_wrong");
}
#[test]
fn gf2_row_drop_aug_check_wrong_refuted() {
    assert_counterexample("gf2_row_drop_aug_check_wrong");
}

// ── ARM B: terminal `.any(..)` — emit UNSAT ⟹ some reduced row is `0 == 1` ───────
#[test]
fn gf2_unsat_detected_verified() {
    assert_verified("gf2_unsat_detected");
}
#[test]
fn gf2_unsat_detected_no_row_wrong_refuted() {
    assert_counterexample("gf2_unsat_detected_no_row_wrong");
}
