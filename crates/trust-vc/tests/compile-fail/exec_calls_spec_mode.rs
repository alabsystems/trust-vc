// Test: exec function calling spec_mode function should fail mode checking (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn exec_caller(x: i32) -> i32 {
    spec_mode_helper(x)
}

#[trust_vc::spec_mode]
fn spec_mode_helper(x: i32) -> i32 {
    x + 1
}

fn main() {}
