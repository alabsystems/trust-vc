// Test: exec function calling exec function via qualified path is legal (#2066).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

mod helpers {
    pub fn add_one(x: i32) -> i32 {
        x + 1
    }
}

fn exec_caller(x: i32) -> i32 {
    helpers::add_one(x)
}

fn main() {
    let _ = exec_caller(5);
}
