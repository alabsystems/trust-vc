// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! THE CONTROL for `broadcast_goal_witness_sort_soundness`: byte-identical goals
//! to the repro fixture with the `u8` broadcast lemma REMOVED. These were
//! refuted before the fix and are refuted after it, so the lemma — not the goal
//! shape — is what turned them.

#![allow(dead_code)]

#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result <= 255u64)]
pub fn fv_any_u64_is_small(w: u64) -> u64 {
    w
}

#[trust_vc::requires(w * w == w * w)]
#[trust_vc::ensures(result <= 255u64)]
pub fn fv_any_u32_is_small(w: u32) -> u32 {
    w
}
