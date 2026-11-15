// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Adversarial soundness suite for the file-path `broadcast_use!` activation
//! lane (un-quarantine #4).
//!
//! Activation is FORWARD-ONLY and MONOTONE. Each `broadcast_use!(g)` lowers to a
//! body-ordered `BroadcastUse` marker; a grouped broadcast axiom for `g` is
//! admissible for a proof obligation A at body position `p` iff a
//! `broadcast_use!(g)` marker exists at a body position `< p`. No group ever
//! activates any obligation earlier than its own use site — the cardinal
//! retroactive false-verify the lane was quarantined for.
//!
//! `bcg` (grouped fixture) is `#[opaque]` and its ONLY axiom is the GROUPED,
//! GUARDED lemma `bc_guarded_pos` (`x > 0 ==> bcg(x) > 0`, gated by
//! `bc_guarded_group`), so nothing about `bcg` is learnable unless the group is
//! active at the goal's position. `bcf` (ungrouped fixture) carries an UNGROUPED
//! (always-active) lemma. The two predicates live in SEPARATE files so the
//! always-active global `forall` never blurs the grouped lane's negative
//! verdicts (see the fixture headers).

use trust_vc_core::{verify_function_from_file, VerifyResult};

const GROUPED: &str = "broadcast_use_soundness_repro.rs";
const UNGROUPED: &str = "broadcast_use_ungrouped_repro.rs";

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn verify(file: &str, function: &str) -> VerifyResult {
    // Disable the persistent on-disk verification cache for this soundness
    // suite. The cache stores only `Verified` results keyed on the prepared
    // context's fingerprint and lives under `target/` (surviving `cargo clean
    // -p`). A soundness probe that asserts a NON-verifying verdict must never
    // trust that cache: a single stale `Verified` — e.g. one written by an
    // incremental build before the position-aware gate was compiled in — would
    // otherwise be served forever and mask a real retroactive false-verify.
    // Recomputing every time is cheap here and keeps the suite's verdicts
    // firsthand. Mirrors `loop_decreases_soundness.rs`.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&fixture(file), function)
            .unwrap_or_else(|err| panic!("`{function}` failed to extract: {err:?}"))
    })
}

fn assert_verified(file: &str, function: &str) {
    match verify(file, function) {
        VerifyResult::Verified => {}
        other => panic!("`{function}` should VERIFY, got {other:?}"),
    }
}

fn assert_counterexample(file: &str, function: &str) {
    match verify(file, function) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("`{function}` should be a Counterexample, got {other:?}"),
    }
}

/// A fail-closed non-`Verified` verdict (Counterexample / NotProved / Unknown).
/// `Verified` is the only unacceptable outcome.
fn assert_not_verified(file: &str, function: &str) {
    if verify(file, function) == VerifyResult::Verified {
        panic!("SOUNDNESS BREACH: `{function}` must NOT verify")
    }
}

// ---------------------------------------------------------------------------
// UNGROUPED — a global (`#[broadcast]`, no group) lemma is always active.
// ---------------------------------------------------------------------------

#[test]
fn ungrouped_broadcast_fires_globally() {
    // `bcf` opaque; ungrouped lemma `bcf(x) == x` fires with NO broadcast_use! ⇒
    // bcf(5) == 5 ⇒ bcf(5) > 0. Must VERIFY (ungrouped is not gated).
    assert_verified(UNGROUPED, "ungrouped_broadcast_activates");
}

// ---------------------------------------------------------------------------
// GROUPED — the filter is live: without a use, the group stays inactive.
// ---------------------------------------------------------------------------

#[test]
fn grouped_broadcast_filtered_without_use() {
    // No broadcast_use!; the grouped axiom is filtered out and `bcg` is opaque
    // with no other axiom ⇒ bcg(5) > 0 is unprovable. Must COUNTEREXAMPLE. A
    // Verified here means a grouped broadcast is always active (broadcast_use!
    // would be meaningless).
    assert_counterexample(GROUPED, "grouped_broadcast_needs_use");
}

#[test]
fn grouped_broadcast_use_before_assert_activates() {
    // POSITIVE CONTROL: broadcast_use! PRECEDES the assert; the guarded axiom
    // activates and at x = 5 the guard 5 > 0 holds ⇒ bcg(5) > 0. Must VERIFY.
    assert_verified(GROUPED, "grouped_broadcast_activated");
}

// ---------------------------------------------------------------------------
// GUARD FOLD (orthogonal, must stay fail-closed) — the `requires` guard is NOT
// dropped: at x = 0 the guard 0 > 0 is false, so the axiom says nothing.
// ---------------------------------------------------------------------------

#[test]
fn dropped_requires_guard_cannot_false_verify() {
    // WITH broadcast_use!, the guarded axiom is (x > 0 ==> bcg(x) > 0). At x = 0
    // the guard is FALSE ⇒ nothing about bcg(0) ⇒ bcg(0) > 0 unprovable. Must
    // FAIL CLOSED. A Verified here means the requires guard was DROPPED — a
    // cardinal false-verify. (Fail-closed as Unknown, not a concrete
    // Counterexample: the live guarded `forall` blocks ay's model validation for
    // the un-refuted goal — sound, just not a model.)
    assert_not_verified(GROUPED, "dropped_requires_guard_false_verify");
}

// ---------------------------------------------------------------------------
// RETROACTIVITY (the cardinal soundness guard) — a use AFTER an assert must NOT
// reach back and activate the group for that earlier assert.
// ---------------------------------------------------------------------------

/// The cardinal false-verify guard for this lane. The assert on `bcg(5) > 0`
/// PRECEDES the `broadcast_use!(bc_guarded_group)`; at the assert's body
/// position the group is not yet active and `bcg` is opaque, so `bcg(5) > 0` is
/// unprovable. A `Verified` here is the retroactive false-verify the lane was
/// quarantined for — a function-global positionless set would produce exactly
/// that.
#[test]
fn broadcast_use_cannot_activate_retroactively() {
    assert_counterexample(GROUPED, "broadcast_use_cannot_activate_retroactively");
}

/// BOUNDARY / SWAP-LINES probe: a single function with two asserts bracketing
/// one use (`assert; broadcast_use!(g); assert`). The PRE-use assert
/// counterexamples at its position (short-circuiting the whole-function
/// verdict), so the function must NOT verify. A POSITIONLESS set activates the
/// group for the whole function ⇒ both asserts pass ⇒ the function VERIFIES,
/// which this test rejects. The POST-use assert verifying at its own position is
/// pinned separately by `grouped_broadcast_use_before_assert_activates`.
/// Together they pin activation AT the use site.
#[test]
fn broadcast_use_boundary_pins_at_use_site() {
    assert_not_verified(GROUPED, "broadcast_use_boundary_pins_at_use_site");
}
