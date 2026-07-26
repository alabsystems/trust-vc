// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb OPTIMIZATION INCUMBENT accept-core soundness
// fixture: `sanitize_optimization_incumbent` (portfolio.rs:5344-5362) ACCEPTS an
// incumbent ONLY WHEN it re-verifies against the ORIGINAL constraints
// (`verify_all_constraints`, the VIG) AND the stored objective is the EXACT
// recompute of the assignment (`eval_objective`, == `eval_objective_exact` on the
// in-range path), never a producer's unchecked claim. This is the VIG core the
// warmup flagged ("the accept path could store an objective without a feasibility
// check"). Each soundness contract PROVES; each unsound control (no VIG check /
// trust the claim / both) is REFUTED. See the fixture header for the modeling.
//
// `tests/fixtures/ay_incumbent_vig_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/incumbent_vig_realbody.rs` in the `ay` repo.
// Override with `AY_PB_INCUMBENT_PROOF_SRC` to verify against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_INCUMBENT_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_incumbent_vig_realbody.rs",
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

// ── P1: ACCEPT ⟹ FEASIBLE (the VIG re-check gates accept) ────────────────────
#[test]
fn incumbent_accepted_verified() {
    assert_verified("incumbent_accepted");
}
#[test]
fn incumbent_accepted_no_check_wrong_refuted() {
    assert_counterexample("incumbent_accepted_no_check_wrong");
}

// ── P2: STORED OBJECTIVE == EXACT RECOMPUTE (claim never trusted blindly) ────
#[test]
fn incumbent_stored_objective_verified() {
    assert_verified("incumbent_stored_objective");
}
#[test]
fn incumbent_stored_objective_trust_claim_wrong_refuted() {
    assert_counterexample("incumbent_stored_objective_trust_claim_wrong");
}

// ── COMBINED: ACCEPT ⟹ (feasible ∧ stored == exact recompute) ────────────────
#[test]
fn incumbent_accept_objective_exact_verified() {
    assert_verified("incumbent_accept_objective_exact");
}
#[test]
fn incumbent_accept_objective_exact_wrong_refuted() {
    assert_counterexample("incumbent_accept_objective_exact_wrong");
}
