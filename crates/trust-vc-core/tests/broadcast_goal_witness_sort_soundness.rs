// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CARDINAL FALSE-VERIFY REGRESSION: a broadcast `forall` instantiated at a
//! GOAL-HARVESTED witness of the wrong sort.
//!
//! This is the SIBLING of `broadcast_out_of_sort_witness_soundness`. That one
//! closed the witness sources that produce integer LITERALS (type boundaries,
//! premise constants, SAT-model scalars) with a value-range filter. Broadcast
//! premises are also instantiated at witness EXPRESSIONS: an interpreted-op
//! dead-trigger lemma is ground-replayed by matching its trigger pattern against
//! the goal and assumption expressions at the IR level, and that match binds the
//! lemma's bound variable to whatever subexpression it finds.
//!
//! Nothing checked that subexpression's type, and the failure mode is WORSE than
//! the literal one. A literal out of range encodes as a visibly false fact
//! (`2^64-1 <= 255`), which at least trips the vacuity guard. A wider-typed
//! EXPRESSION encodes as a perfectly consistent, perfectly unjustified fact:
//! `forall|x: u8| x <= 255u8` matched against `w * w` for a `u64 w` asserts
//! `w <= 255`. So
//!
//! ```ignore
//! fn fv_any_u64_is_small(w: u64) -> u64 { w }   // ensures result <= 255u64
//! ```
//!
//! came back `Verified`. Nothing is contradictory, so no vacuity check fires.
//!
//! The fix routes EVERY witness source through one gate
//! (`encoder::witness_sort::instantiate_bound_vars_in_sort`) rather than
//! filtering each source where it happens to be produced — see that module for
//! the full source inventory (S1–S7).
//!
//! NARROWNESS. The gate is a sort-membership test, not "reject goal-harvested
//! witnesses" and not "disable interpreted-op triggers". The `pin_*` cases are
//! proofs reachable ONLY through a goal-harvested SYMBOLIC witness, plus a
//! discriminator that must still fail.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const REPRO: &str = "broadcast_goal_witness_sort_repro.rs";
const CONTROL: &str = "broadcast_goal_witness_sort_control.rs";
const PINS: &str = "broadcast_goal_witness_sort_pins.rs";

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// The on-disk VC cache stores only `Verified` results and survives
/// `cargo clean -p`. A soundness probe asserting a NON-verified verdict must
/// never trust it: one stale `Verified` written by a pre-fix binary would mask
/// the regression forever.
fn verify_in(file: &str, function: &str) -> VerifyResult {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&fixture(file), function)
            .unwrap_or_else(|err| panic!("`{function}` failed to extract: {err:?}"))
    })
}

fn assert_not_verified(file: &str, function: &str) {
    if let VerifyResult::Verified = verify_in(file, function) {
        panic!(
            "SOUNDNESS BREACH: `{function}` must NOT verify — the postcondition is false, \
             and only an out-of-sort broadcast instance can discharge it"
        );
    }
}

fn assert_verified(file: &str, function: &str) {
    match verify_in(file, function) {
        VerifyResult::Verified => {}
        other => panic!("NARROWNESS PIN BROKEN: `{function}` should VERIFY, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The defect. `f(w) = w` cannot satisfy `result <= 255` for `w > 255`.
// ---------------------------------------------------------------------------

#[test]
fn a_u64_identity_is_not_bounded_by_255() {
    assert_not_verified(REPRO, "fv_any_u64_is_small");
}

/// The same defect at a second width, so a width-specific patch cannot pass.
#[test]
fn a_u32_identity_is_not_bounded_by_255() {
    assert_not_verified(REPRO, "fv_any_u32_is_small");
}

/// Sharper than "did not verify": the engine must actually produce the
/// refutation. A fix that merely turned the false verify into `Unknown` would
/// satisfy the two tests above; this one pins that the counterexample survives.
#[test]
fn the_false_goal_is_refuted_not_merely_unproven() {
    for function in ["fv_any_u64_is_small", "fv_any_u32_is_small"] {
        match verify_in(REPRO, function) {
            VerifyResult::Counterexample { .. } => {}
            other => panic!("`{function}` should be refuted with a model, got {other:?}"),
        }
    }
}

/// THE CONTROL. Same goals, lemma removed. Refuted before the fix and after it,
/// so the broadcast lemma — not the goal shape — is what turned them. Without
/// this the suite could not tell "the fix works" from "these never verified".
#[test]
fn control_without_the_lemma_refutes_both() {
    for function in ["fv_any_u64_is_small", "fv_any_u32_is_small"] {
        if let VerifyResult::Verified = verify_in(CONTROL, function) {
            panic!(
                "CONTROL BROKEN: `{function}` verified with NO lemma in scope — the repro no \
                 longer isolates the broadcast lemma"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the goal-harvested witness path must still work.
// ---------------------------------------------------------------------------

/// The pin that distinguishes this fix from "stop harvesting witnesses from the
/// goal". `g` is opaque and never revealed and `w` is symbolic, so no literal
/// witness battery can prove `g(w) == w`; the only route is binding the lemma's
/// bound variable to the goal's symbolic `w`.
#[test]
fn goal_harvested_symbolic_witness_still_fires() {
    assert_verified(PINS, "pin_goal_witness_fires");
}

/// Discriminator for the pin above, so it cannot be passing on a contradictory
/// context instead of on the lemma.
#[test]
fn goal_harvested_witness_does_not_prove_a_false_goal() {
    assert_not_verified(PINS, "pin_discriminator_off_by_one");
}

/// The gate reads a witness's inferred type, not just bare variables: a cast
/// expression of the right type is still a legitimate instantiation.
#[test]
fn cast_shaped_witness_still_fires() {
    assert_verified(PINS, "pin_cast_witness_fires");
}
