// Test: exec function calling proof function via self:: should fail mode checking (#2066).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn exec_caller(x: i32) -> i32 {
    self::proof_helper(x);
    x
}

#[trust_vc::proof]
fn proof_helper(x: i32) {
    let _ = x + 1;
}

fn main() {}
