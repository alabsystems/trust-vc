// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb PIGEONHOLE / HALL UNSAT detector
// accept-decision fixture: `pigeonhole_unsat_cp_checked` (pigeonhole.rs:858-860)
// returns `true` (=> the caller may emit `s UNSATISFIABLE`) ONLY WHEN a
// constructed cutting-planes `Refutation` was CERTIFIED by the kernel-verified
// `Refutation::check` — each builder gates its `Some` on `refutation.check().ok()?`
// (pigeonhole.rs:304 / 802), and the top-level gate is `pure.is_some() ||
// hall.is_some()`. Each soundness contract PROVES; each unsound control (drop a
// builder's checker gate) is REFUTED. See the fixture header.
//
// `tests/fixtures/ay_pigeonhole_gate_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/pigeonhole_gate_realbody.rs` in the `ay` repo.
// Override with `AY_PB_PIGEONHOLE_PROOF_SRC` to verify directly against an `ay`
// checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_PIGEONHOLE_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_pigeonhole_gate_realbody.rs",
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

// ── PER-BUILDER GATE: emit refutation ⟹ Refutation::check accepted ──────────────
#[test]
fn refutation_emit_some_verified() {
    assert_verified("refutation_emit_some");
}
#[test]
fn refutation_emit_some_no_check_wrong_refuted() {
    assert_counterexample("refutation_emit_some_no_check_wrong");
}

// ── TOP-LEVEL GATE: report UNSAT ⟹ some refutation was kernel-checked ───────────
#[test]
fn pigeonhole_unsat_emitted_verified() {
    assert_verified("pigeonhole_unsat_emitted");
}
#[test]
fn pigeonhole_unsat_emitted_pure_no_check_wrong_refuted() {
    assert_counterexample("pigeonhole_unsat_emitted_pure_no_check_wrong");
}
