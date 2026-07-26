// Test: spec function calling exec helper should fail mode checking.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn exec_helper(x: i32) -> i32 {
    x + 1
}

#[trust_vc::spec]
fn illegal_spec_call(x: i32) -> i32 {
    exec_helper(x)
}

fn main() {}
