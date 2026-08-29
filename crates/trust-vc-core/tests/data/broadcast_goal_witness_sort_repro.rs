// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fixture for `broadcast_goal_witness_sort_soundness` — THE DEFECT.
//!
//! `lem_x` is a legitimate, trivially TRUE broadcast lemma over a `u8`. Its
//! interpreted-op trigger (`x * x`) routes it to the ground-replay path, which
//! instantiates it by matching the trigger against the goal/assumption
//! expressions at the IR level. That match binds `x` to whatever subexpression
//! it finds — here the `u64` (resp. `u32`) product `w * w` — so the lemma was
//! instantiated at a witness that is NOT a `u8`, asserting `w <= 255` about an
//! arbitrary `u64`.
//!
//! Nothing about that is contradictory, so the vacuity guard cannot see it. It
//! is simply an unjustified fact, and it makes an obviously false postcondition
//! come back `Verified`.
//!
//! Kept free of any other lemma so the refutation is a clean counterexample and
//! the pins cannot interfere. The narrowness pins live in
//! `broadcast_goal_witness_sort_pins.rs`.

#![allow(dead_code)]

#[trust_vc::broadcast]
#[trust_vc::trigger(x * x)]
fn lem_x(x: u8) {
    trust_vc::ensures!(x <= 255u8);
}

/// `f(w) = w`, so `result <= 255` is false for every `w > 255`. The control
/// refutes it with `w = u64::MAX`.
#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result <= 255u64)]
pub fn fv_any_u64_is_small(w: u64) -> u64 {
    w
}

/// The same defect at a second width, so a width-specific patch cannot pass.
#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result <= 255u64)]
pub fn fv_any_u32_is_small(w: u32) -> u32 {
    w
}
