// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Adversarial soundness suite for the file-path `loop_decreases!` lane
//! (un-quarantine #3).
//!
//! Termination is proven by a WELL-FOUNDED-MEASURE invariant: for each measure
//! `M`, guard `G`, and loop invariant `Inv`, two INDEPENDENT obligations —
//!
//!   WF1 (non-negativity FLOOR): `Inv(s) && G(s) |= M(s) >= 0`, a DIRECT
//!   single-state entailment in the measure's int sort. NOT an inductive step
//!   (which would vacuously assume the floor at the pre-state under a negative
//!   invariant), and NOT delegated to the overflow/underflow pass.
//!
//!   WF2 (strict DESCENT): `Inv(s) && G(s) && s'=f(s) |= M(s') < M(s)`, a
//!   frame-condition inductive step whose entry var is bound (not free) from the
//!   exact single-iteration transition.
//!
//! The cardinal case is `unbounded_negative_measure` (a strictly-decreasing but
//! unbounded-below mathematical `int`): WF2 holds (it DOES decrease) yet the
//! loop does NOT terminate, so ONLY WF1 can reject it. A `Verified` there is the
//! false-verify this lane was quarantined for.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const REPRO: &str = "loop_decreases_soundness_repro.rs";

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn verify(function: &str) -> VerifyResult {
    // Disable the persistent on-disk verification cache for this soundness
    // suite. The cache stores only `Verified` results keyed on the prepared
    // context's fingerprint and lives under `target/` (surviving `cargo clean
    // -p`). A soundness probe that asserts a NON-verifying verdict must never
    // trust that cache: a single stale `Verified` — e.g. one written by an
    // incremental build before this WF1 floor was compiled in — would otherwise
    // be served forever and mask a real false-verify. Recomputing every time is
    // cheap here and keeps the suite's verdicts firsthand.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&fixture(REPRO), function)
            .unwrap_or_else(|err| panic!("`{function}` failed to extract: {err:?}"))
    })
}

fn assert_verified(function: &str) {
    match verify(function) {
        VerifyResult::Verified => {}
        other => panic!("`{function}` should VERIFY (genuinely terminating), got {other:?}"),
    }
}

/// A fail-closed non-`Verified` verdict (Counterexample / NotProved / Unknown).
/// `Verified` is the only unacceptable outcome.
fn assert_not_verified(function: &str) {
    match verify(function) {
        VerifyResult::Verified => {
            panic!("SOUNDNESS BREACH: `{function}` must NOT verify (non-terminating / bad measure)")
        }
        _ => {}
    }
}

fn assert_counterexample(function: &str) {
    match verify(function) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("`{function}` should be a Counterexample, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// POSITIVE — genuinely terminating loops verify (no over-rejection).
// ---------------------------------------------------------------------------

#[test]
fn terminating_countup_verifies() {
    assert_verified("terminating_countup");
}

#[test]
fn terminating_countdown_verifies() {
    assert_verified("terminating_countdown");
}

// ---------------------------------------------------------------------------
// NEGATIVE (strict descent, WF2) — a non-decreasing measure is rejected.
// ---------------------------------------------------------------------------

#[test]
fn bad_measure_increases_is_counterexample() {
    assert_counterexample("bad_measure_increases");
}

// ---------------------------------------------------------------------------
// NEGATIVE (floor, WF1) — a measure that decreases below zero is rejected.
// ---------------------------------------------------------------------------

#[test]
fn measure_goes_negative_is_counterexample() {
    // u64 measure `5 - i`: once i > 5 the measure goes negative. Caught by the
    // WF1 floor (`5 - i >= 0` is unprovable from the invariant `i <= 10`).
    assert_counterexample("measure_goes_negative");
}

/// The cardinal false-verify guard: a strictly-decreasing `int` measure with no
/// lower bound. WF2 (descent) holds, so ONLY the well-foundedness floor can
/// reject it — and it MUST NOT be `Verified`. This loop DIVERGES, so the
/// whole-function vacuous-truth precheck intercepts it (`requires(i < 0)`
/// contradicts the normal-exit fact `i >= 0`) and reports Unknown; the direct
/// WF1 refutation is exercised by `int_floor_probe` below. Either way, a
/// `Verified` here is the cardinal false-verify the lane was quarantined for.
#[test]
fn unbounded_negative_measure_never_verifies() {
    match verify("unbounded_negative_measure") {
        VerifyResult::Verified => panic!(
            "CARDINAL FALSE-VERIFY: `unbounded_negative_measure` decreases forever below zero \
             but was accepted as terminating"
        ),
        _ => {}
    }
}

/// WF1 is load-bearing, demonstrated directly on an `int` measure. A NON-divergent
/// loop (guard `i > -5` broader than invariant `i <= 10`, so it exits) whose
/// measure `i` strictly DECREASES (WF2 holds) but goes NEGATIVE — refuted by the
/// WF1 floor `i >= 0` in the measure's own `int` sort. With WF1 removed, WF2
/// alone would falsely accept it, so the Counterexample MUST come VIA WF1.
#[test]
fn int_floor_probe_is_counterexample_via_wf1() {
    match verify("int_floor_probe") {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            assert!(
                obligation_name.contains("non-negative"),
                "int_floor_probe must be rejected by the WF1 non-negativity FLOOR, but the \
                 counterexample came from `{obligation_name}` — if this names the strict-descent \
                 obligation, WF1 is not load-bearing and the floor is a false tautology"
            );
        }
        VerifyResult::Verified => panic!(
            "FLOOR NOT PROVEN: `int_floor_probe` decreases below zero but was accepted — the WF1 \
             floor is missing or a vacuous tautology"
        ),
        other => panic!("`int_floor_probe` should be a WF1 Counterexample, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// LANDMINE (non-flat body) — no exact transition ⇒ free entry var ⇒ fail closed.
// ---------------------------------------------------------------------------

#[test]
fn continue_skips_measure_fails_closed() {
    // Bare `loop{}` with a `continue` back-edge: no loop context, no captured
    // transition, so the decrease keeps a free entry variable and fails closed.
    assert_not_verified("continue_skips_measure");
}

#[test]
fn break_interior_non_flat_fails_closed() {
    // `if { break }` makes the body non-flat ⇒ `capture_transitions == false` ⇒
    // no measure metadata registered ⇒ free entry variable ⇒ fails closed.
    assert_not_verified("break_interior_non_flat");
}
