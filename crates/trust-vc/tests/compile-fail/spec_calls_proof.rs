// Test: spec function calling proof function should fail mode checking.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::proof]
fn proof_helper(x: i32) {
    let _ = x + 1;
}

#[trust_vc::spec]
fn illegal_spec_calls_proof(x: i32) -> i32 {
    proof_helper(x);
    x
}

fn main() {}
