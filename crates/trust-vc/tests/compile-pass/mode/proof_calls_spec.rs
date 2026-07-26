// Test: proof function can call spec function.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

#[trust_vc::spec]
fn spec_helper(x: i32) -> i32 {
    x + 1
}

#[trust_vc::proof]
fn proof_caller(x: i32) {
    let _ = spec_helper(x);
}

fn main() {}
