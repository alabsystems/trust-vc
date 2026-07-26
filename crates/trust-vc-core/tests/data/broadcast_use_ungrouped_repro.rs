// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixture for the UNGROUPED (global) file-path broadcast lane. `bcf` is OPAQUE
// (uninterpreted unless a broadcast axiom fires) and carries an UNGROUPED
// `#[broadcast]` lemma, which is globally active — no `broadcast_use!` is needed.
//
// Kept SEPARATE from the grouped fixture (`broadcast_use_soundness_repro.rs`):
// this global `forall` is active in every function, and its mere presence in a
// context whose goal is about a DIFFERENT (grouped) predicate leaves it
// un-instantiated, which drives ay's candidate-model validation to `Unknown`
// rather than a concrete `Counterexample`. Isolating the ungrouped lemma keeps
// the grouped lane's negative verdicts precise.
//
// Verified via `verify_function_from_file` in `broadcast_use_soundness.rs`.

#[trust_vc::opaque]
#[trust_vc::spec]
fn bcf(x: int) -> int {
    x
}

// Ungrouped #[broadcast] lemma over `bcf`: globally active (no broadcast_use!).
#[trust_vc::broadcast]
#[trust_vc::trigger(bcf(x))]
fn bc_global_pos(x: int) {
    trust_vc::ensures!(bcf(x) == x);
}

// STEP A probe: the ungrouped global axiom fires ⇒ bcf(5) == 5 ⇒ bcf(5) > 0.
// Should VERIFY without any broadcast_use! (ungrouped broadcasts are not gated).
#[trust_vc::ensures(true)]
fn ungrouped_broadcast_activates() {
    trust_vc::assert!(bcf(5) > 0);
}
