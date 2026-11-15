// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fixture for the THIRD Unknown category: ay's independent model-check gate
//! catching its OWN invalid model.
//!
//! Shape (ay defect A, `docs/ay-defect-2026-09-17-quantified-axiom-family.md`
//! section 3): a top-level definitional `forall` whose body READS THE BOUND
//! VARIABLE, relating an uninterpreted function to a linear-arithmetic term,
//! with NO ground instance for the instantiation lane to fire on. ay publishes
//! a model, its own gate ground-falsifies the axiom under that model, and ay
//! fail-closes `Sat -> Unknown` (which is ay behaving CORRECTLY).
//!
//! The discriminator measured by that investigation is that the body reads the
//! binder, NOT that the true-set is infinite: `i == 5` triggers it too. One
//! ground instance (`p_ground` below) removes it entirely.
//!
//! DO NOT add an `assert!(g(7))`-style ground instance to `t_gate_rejected`:
//! that is precisely what makes the gate stop firing, and the probe stops
//! probing.

use trust_vc_types::int;

// ── the trigger: binder-reading definitional body, no ground instance ──

#[trust_vc::spec]
fn g(i: int) -> bool {
    5 <= i
}

/// Triggers ay's model gate. The goal is VALID (`choose` of `g` yields an `i`
/// with `5 <= i` by `g`'s own definition), but trust-vc cannot discharge it
/// here, and the reason is the caught invalid model — not a refutation.
#[trust_vc::ensures(true)]
fn t_gate_rejected() {
    let i: int = trust_vc::choose!(|i: int| g(i));
    trust_vc::assert!(5 <= i);
}

// ── control 1: a GENUINE refutation still reports as a Counterexample ──

/// No quantified definitional axiom at all; a plainly false ground arithmetic
/// claim. Must stay a `Counterexample` WITH a model.
#[trust_vc::ensures(true)]
fn c_real_counterexample(x: int) {
    trust_vc::assume!(x == 3);
    trust_vc::assert!(x == 4);
}

// ── control 2: the same shape WITH a ground instance verifies ──

/// The report's `p_ge5` probe: one ground instance gives the instantiation
/// lane something to fire on and the gate never fires.
#[trust_vc::ensures(true)]
fn p_ground() {
    trust_vc::assert!(g(7));
}
