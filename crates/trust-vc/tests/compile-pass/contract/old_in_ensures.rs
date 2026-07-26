// Test: old!() works inside attribute ensures clauses.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(
    requires(x > 0),
    ensures(ret == old!(x) + 1),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = increment(5);
}
