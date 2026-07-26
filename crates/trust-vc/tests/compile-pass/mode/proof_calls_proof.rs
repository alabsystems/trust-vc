// Test: proof function can call another proof function.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

#[trust_vc::proof]
fn inner_proof(x: i32) {
    let _ = x + 1;
}

#[trust_vc::proof]
fn outer_proof(x: i32) {
    inner_proof(x);
}

fn main() {}
