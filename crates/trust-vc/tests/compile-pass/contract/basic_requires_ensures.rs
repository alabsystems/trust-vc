// Test: basic #[trust_vc::contract] with requires and ensures compiles.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(
    requires(x > 0),
    ensures(ret > 0),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = increment(5);
}
