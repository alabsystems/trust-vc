// Test: spec_mode function calling exec function should fail mode checking (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn exec_helper(x: i32) -> i32 {
    x + 1
}

#[trust_vc::spec_mode]
fn illegal_spec_mode_call(x: i32) -> i32 {
    exec_helper(x)
}

fn main() {}
