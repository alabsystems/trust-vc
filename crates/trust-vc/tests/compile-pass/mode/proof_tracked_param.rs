// Test: proof function with Tracked<T> parameter type.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Part of #2427 Slice 3: Tracked<T> parameters in proof functions carry
// proof-mode ownership. Non-Copy Tracked<T> values enforce linear consumption
// via Rust's borrow checker. The `tracked` keyword modifier works at the
// token-stream level (proc macro codegen) but not in real Rust source; user
// code uses the Tracked<T> type wrapper instead.

#![deny(warnings)]

use trust_vc_types::Tracked;

#[trust_vc::proof]
fn proof_with_tracked_type(tok: Tracked<i32>) {
    let _ = tok;
}

#[trust_vc::proof]
fn proof_with_mixed_tracked(tok: Tracked<i32>, x: i32) {
    let _ = tok;
    let _ = x + 1;
}

// Non-Copy Tracked<T> enforces linear consumption:
// Tracked<String> is NOT Copy, so `tok` can only be used once.
#[trust_vc::proof]
fn proof_tracked_linear(tok: Tracked<String>) {
    let _consumed = tok; // moved, cannot reuse
}

fn main() {}
