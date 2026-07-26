// Test: exec function calling spec function via plain multi-segment path
// should fail mode checking (#2066).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod specs {
    #[trust_vc::spec]
    pub fn helper(x: i32) -> i32 { x + 1 }
}

fn exec_caller(x: i32) -> i32 {
    specs::helper(x)
}

fn main() {}
