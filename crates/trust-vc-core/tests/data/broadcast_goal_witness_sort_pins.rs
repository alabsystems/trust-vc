// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! NARROWNESS PINS for `broadcast_goal_witness_sort_soundness`.
//!
//! These are what stop the fix from being "drop every goal-harvested witness",
//! which would pass every soundness test and be a capability disaster.
//!
//! `g` is `#[opaque]` and never revealed, and `w` is SYMBOLIC — so the fixed
//! type-boundary battery (0, 1, `u64::MAX`) and the premise-constant battery
//! cannot discharge `g(w) == w`. The ONLY route to a proof is the interpreted-op
//! trigger match against the goal's `w * w`, binding the lemma's bound variable
//! to the symbolic `w`: exactly the substitution the fix gates. If the gate
//! over-rejects, `pin_goal_witness_fires` goes red.

#![allow(dead_code)]

#[trust_vc::opaque]
#[trust_vc::spec]
fn g(v: u64) -> u64 {
    v
}

#[trust_vc::broadcast]
#[trust_vc::trigger(x * x)]
fn lem_g(x: u64) {
    trust_vc::ensures!(g(x) == x);
}

#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result == w)]
pub fn pin_goal_witness_fires(w: u64) -> u64 {
    g(w)
}

/// Discriminator for the pin above: the lemma fires, but `g(w) == w + 1` is
/// false. Without this, "the pin passes" would also be satisfied by a
/// contradictory context.
#[trust_vc::requires(w < 1000u64)]
#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result == w + 1u64)]
pub fn pin_discriminator_off_by_one(w: u64) -> u64 {
    g(w)
}

/// The witness here is the CAST expression `n as u64`, harvested from the goal
/// exactly like the symbolic case above. It pins that the gate reads a witness's
/// inferred type rather than only recognising bare variables.
#[trust_vc::requires((n as u64) * (n as u64) == (n as u64) * (n as u64))]
#[trust_vc::ensures(result == n as u64)]
pub fn pin_cast_witness_fires(n: u8) -> u64 {
    g(n as u64)
}
