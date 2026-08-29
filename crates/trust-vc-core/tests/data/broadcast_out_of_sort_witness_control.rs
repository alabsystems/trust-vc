// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CONTROL for `broadcast_out_of_sort_witness_soundness`.
//!
//! Byte-for-byte the same three goals as
//! `broadcast_out_of_sort_witness_repro.rs`, with the broadcast lemma REMOVED
//! and nothing else changed. These were refuted both before and after the fix,
//! which is what isolates the lemma as the cause: the goals are not unprovable
//! because of the goal shape or `h`'s opacity handling, they are unprovable
//! full stop, and only the lemma's out-of-sort ground instance ever turned them.
//!
//! A control lives in its own file because `#[trust_vc::broadcast]` publishes a
//! FILE-GLOBAL axiom — a "control" function sharing a file with the lemma would
//! sit in the same poisoned context.

#![allow(dead_code)]

#[trust_vc::opaque]
#[trust_vc::spec]
fn h(v: u64) -> u64 {
    v
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
