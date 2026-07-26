// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the file-path `broadcast_use!` activation adversarial soundness
// suite (grouped lane). `bcg` is OPAQUE (uninterpreted unless a broadcast axiom
// fires) and its ONLY axiom is the GROUPED, GUARDED lemma `bc_guarded_pos`
// (`x > 0 ==> bcg(x) > 0`, gated by group `bc_guarded_group`), so nothing about
// `bcg` is learnable unless the group is active at the goal's body position —
// isolating the position filter and the guard fold.
//
// The UNGROUPED (global) case lives in `broadcast_use_ungrouped_repro.rs`,
// deliberately kept in a SEPARATE file: an always-active global `forall` about
// an UNRELATED predicate stays in every function's context and, being
// uninstantiated for a `bcg` goal, drives ay's candidate-model validation to
// `Unknown` instead of a clean `Counterexample`. Isolating the grouped lane
// keeps its negative verdicts precise.
//
// Verified via `verify_function_from_file` in `broadcast_use_soundness.rs`.

#[trust_vc::opaque]
#[trust_vc::spec]
fn bcg(x: int) -> int {
    x
}

// Grouped, GUARDED lemma over `bcg`: requires x > 0, ensures bcg(x) > 0.
// Publishes forall x. (x > 0 ==> bcg(x) > 0), gated by group `bc_guarded_group`.
// There is NO ungrouped axiom about `bcg`, so it is the ONLY way to learn
// anything about bcg — isolating the filter and guard tests.
#[trust_vc::broadcast_group(bc_guarded_group)]
#[trust_vc::broadcast]
#[trust_vc::trigger(bcg(x))]
fn bc_guarded_pos(x: int) {
    trust_vc::requires!(x > 0);
    trust_vc::ensures!(bcg(x) > 0);
}

// STEP B negative (the FILTER is live): WITHOUT broadcast_use!, the grouped
// axiom is filtered out, and bcg is opaque with no other axiom, so bcg(5) > 0 is
// unprovable. Should COUNTEREXAMPLE. If it VERIFIES, the group filter is broken
// (a grouped broadcast is always active — broadcast_use! would be meaningless).
#[trust_vc::ensures(true)]
fn grouped_broadcast_needs_use() {
    trust_vc::assert!(bcg(5) > 0);
}

// STEP B positive: WITH broadcast_use! BEFORE the assert, the guarded axiom
// activates; at x = 5 the guard 5 > 0 holds ⇒ bcg(5) > 0. Should VERIFY.
#[trust_vc::ensures(true)]
fn grouped_broadcast_activated() {
    trust_vc::broadcast_use!(bc_guarded_group);
    trust_vc::assert!(bcg(5) > 0);
}

// SOUNDNESS (dropped-requires false-verify, guard fold): WITH broadcast_use!,
// the guarded axiom is (x > 0 ==> bcg(x) > 0). At x = 0 the guard 0 > 0 is FALSE,
// so the axiom says nothing about bcg(0), and bcg is opaque ⇒ bcg(0) > 0 is
// unprovable. Must FAIL CLOSED (never Verified). If it VERIFIES, the requires
// guard was DROPPED (a cardinal false-verify). (The verdict is a fail-closed
// Unknown rather than a Counterexample: the live guarded `forall` cannot be
// model-validated by ay for the un-refuted goal — sound, just not a concrete
// model.)
#[trust_vc::ensures(true)]
fn dropped_requires_guard_false_verify() {
    trust_vc::broadcast_use!(bc_guarded_group);
    trust_vc::assert!(bcg(0) > 0);
}

// RETROACTIVITY (the cardinal soundness guard): a block-local activation must
// not be applied to assertions that occur BEFORE the activation site. The assert
// bcg(5) > 0 PRECEDES broadcast_use!(bc_guarded_group), so at the assert's body
// position the group is not yet active and bcg is opaque ⇒ bcg(5) > 0 is
// unprovable ⇒ COUNTEREXAMPLE. A Verified here is the retroactive false-verify
// the lane was quarantined for (a function-global positionless set produces
// exactly that).
#[trust_vc::ensures(true)]
fn broadcast_use_cannot_activate_retroactively() {
    trust_vc::assert!(bcg(5) > 0);
    trust_vc::broadcast_use!(bc_guarded_group);
}

// BOUNDARY / SWAP-LINES probe: two asserts BRACKET one use. The PRE-use assert
// (line below the fn header) sits BEFORE `broadcast_use!`, so at its position
// `bc_guarded_group` is not yet active and `bcg` is opaque ⇒ it COUNTEREXAMPLES
// (the whole-function verdict short-circuits there). The POST-use assert would
// VERIFY at its own position (pinned by `grouped_broadcast_activated`). A
// POSITIONLESS set activates the group for the WHOLE function, so both asserts
// pass and the function VERIFIES — which this fixture must never do. This pins
// the activation boundary AT the use site: any-use-anywhere flipping the whole
// function cannot pass.
#[trust_vc::ensures(true)]
fn broadcast_use_boundary_pins_at_use_site() {
    trust_vc::assert!(bcg(5) > 0);
    trust_vc::broadcast_use!(bc_guarded_group);
    trust_vc::assert!(bcg(5) > 0);
}
