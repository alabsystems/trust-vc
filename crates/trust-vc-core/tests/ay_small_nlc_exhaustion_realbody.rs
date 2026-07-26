// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb SMALL-NLC EXHAUSTIVE-OPTIMUM whole-loop
// soundness fixture: `try_small_nlc_exhaustive_optimum` (portfolio.rs:1094-1147)
// claims OPTIMUM only when the `2^n`-leaf enumeration COMPLETED and `best` is the
// running minimum over EVERY feasible leaf (= the global optimum). The lift is
// delivered as (i) the per-step running-min crux (non-increasing + bounded by the
// folded leaf), (ii) an ACTUAL trust-vc `while` loop maintaining the lower-bound
// invariant across symbolic-`n` iterations, (iii) the COMPLETION terminal forcing
// `best == opt`, plus the post-loop DECISION GATE. Each soundness contract PROVES;
// each unsound control (skip a leaf / drop completion / drop the feasibility
// re-check) is REFUTED. See the fixture header for the entailment model and scope.
//
// `tests/fixtures/ay_small_nlc_exhaustion_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/small_nlc_exhaustion_realbody.rs` in the `ay` repo.
// Override with `AY_PB_SMALL_NLC_PROOF_SRC` to verify directly against an `ay`
// checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_SMALL_NLC_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_small_nlc_exhaustion_realbody.rs",
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

fn assert_not_verified(name: &str) {
    let v = verify(name);
    assert!(
        !matches!(v, VerifyResult::Verified),
        "{name} (unsound control) MUST NOT verify; got {v:?}"
    );
}

// ── (i) PER-STEP CRUX: the running-min update ──────────────────────────────────
#[test]
fn min_update_verified() {
    assert_verified("min_update");
}
#[test]
fn min_update_keep_best_wrong_refuted() {
    assert_counterexample("min_update_keep_best_wrong");
}

// ── (ii) THE WHOLE ENUMERATION LOOP — monotone-preservation inductive proof ────
#[test]
fn exhaustion_best_monotone_verified() {
    assert_verified("exhaustion_best_monotone");
}
#[test]
fn exhaustion_best_monotone_unsound_not_verified() {
    // Overwriting `best` unconditionally can raise it above `start_best`, breaking
    // monotonicity at the inductive step, so the SAME contract does NOT verify.
    assert_not_verified("exhaustion_best_monotone_unsound");
}

// ── (iii) COMPLETION TERMINAL: completed + bounds ⟹ best == opt ────────────────
#[test]
fn exhaustion_completion_forces_global_min_verified() {
    assert_verified("exhaustion_completion_forces_global_min");
}
#[test]
fn exhaustion_drop_completion_wrong_refuted() {
    assert_counterexample("exhaustion_drop_completion_wrong");
}

// ── POST-LOOP DECISION GATE: emit OPTIMUM ⟹ all re-checks held ─────────────────
#[test]
fn exhaustion_emit_optimum_verified() {
    assert_verified("exhaustion_emit_optimum");
}
#[test]
fn exhaustion_emit_drop_completion_wrong_refuted() {
    assert_counterexample("exhaustion_emit_drop_completion_wrong");
}
#[test]
fn exhaustion_emit_drop_feasible_wrong_refuted() {
    assert_counterexample("exhaustion_emit_drop_feasible_wrong");
}
