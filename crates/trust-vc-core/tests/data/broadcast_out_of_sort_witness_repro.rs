// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fixture for `broadcast_out_of_sort_witness_soundness`.
//!
//! `h` is `#[opaque]` and never revealed, so NOTHING about `h(0)` is derivable.
//! The three `fv_*` postconditions below are mutually contradictory: at most one
//! can hold, so any two of them verifying is a proof that the context is
//! contradictory. All three verified before the fix.
//!
//! The poison came from the broadcast lemma: `lem_x` is trivially TRUE and
//! legitimately published, but its bound variable is a NARROW `u8` while the
//! model witnesses harvested for instantiation came from `u64` terms. The
//! interpreted-op trigger (`x * x`) routes the lemma to the ground-replay /
//! model-revalidation path where those witnesses are substituted.

#![allow(dead_code)]

#[trust_vc::opaque]
#[trust_vc::spec]
fn h(v: u64) -> u64 {
    v
}

#[trust_vc::broadcast]
#[trust_vc::trigger(x * x)]
fn lem_x(x: u8) {
    trust_vc::ensures!(x <= 255u8);
}

#[trust_vc::ensures(result == 42u64)]
pub fn fv_forty_two() -> u64 {
    h(0u64)
}

#[trust_vc::ensures(result == 43u64)]
pub fn fv_forty_three() -> u64 {
    h(0u64)
}

#[trust_vc::ensures(result == 0u64)]
pub fn fv_zero() -> u64 {
    h(0u64)
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — a legitimate narrow-typed broadcast lemma with an
// interpreted-op trigger must STILL fire and prove what it is supposed to.
// These go through the very function the fix filters
// (`build_premise_ground_instances`), via its fixed type-boundary battery.
// ---------------------------------------------------------------------------

#[trust_vc::opaque]
#[trust_vc::spec]
fn hh(v: u8) -> u8 {
    v
}

#[trust_vc::broadcast]
#[trust_vc::trigger(x * x)]
fn lem_hh(x: u8) {
    trust_vc::ensures!(hh(x) == x);
}

#[trust_vc::ensures(result == 0u8)]
pub fn pin_boundary_zero() -> u8 {
    hh(0u8)
}

#[trust_vc::ensures(result == 1u8)]
pub fn pin_boundary_one() -> u8 {
    hh(1u8)
}

#[trust_vc::ensures(result == 255u8)]
pub fn pin_boundary_max() -> u8 {
    hh(255u8)
}

/// Discriminator for the pins above: the lemma fires, but `hh(0) == 1` is false,
/// so this must NOT verify. Without it, "the pins pass" would be satisfied by a
/// contradictory context too.
#[trust_vc::ensures(result == 1u8)]
pub fn pin_discriminator_wrong_value() -> u8 {
    hh(0u8)
}
