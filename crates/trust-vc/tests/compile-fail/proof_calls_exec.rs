// Test: proof function calling exec helper should fail mode checking.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn exec_helper(x: i32) -> i32 {
    x + 1
}

#[trust_vc::proof]
fn illegal_proof_call(x: i32) {
    let _ = exec_helper(x);
}

fn main() {}
