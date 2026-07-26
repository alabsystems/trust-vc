// Test: exec function calling exec helper remains valid.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

fn exec_helper(x: i32) -> i32 {
    x + 1
}

fn exec_caller(x: i32) -> i32 {
    exec_helper(x)
}

fn main() {
    let _ = exec_caller(5);
}
