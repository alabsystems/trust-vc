// Test: all four contract clauses together.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(
    requires(n > 0),
    ensures(ret >= 1),
    returns(ret),
    decreases(n),
)]
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
    let _ = factorial(5);
}
