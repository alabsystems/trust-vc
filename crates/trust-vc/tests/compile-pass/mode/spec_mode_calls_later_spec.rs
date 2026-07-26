// Test: spec_mode function can call a later-defined spec function (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code, unexpected_cfgs)]

#[trust_vc::spec_mode]
fn spec_mode_caller(x: i32) -> i32 {
    spec_helper(x)
}

#[trust_vc::spec]
fn spec_helper(x: i32) -> i32 {
    x + 1
}

fn main() {}
