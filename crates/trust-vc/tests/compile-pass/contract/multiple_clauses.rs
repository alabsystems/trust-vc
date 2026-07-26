// Test: multiple conditions in one requires clause.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(requires(x > 0, x < 100))]
fn bounded(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = bounded(50);
}
