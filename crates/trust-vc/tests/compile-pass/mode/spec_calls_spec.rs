// Test: spec function can call another spec function.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

#[trust_vc::spec]
fn inner_spec(x: i32) -> i32 {
    x + 1
}

#[trust_vc::spec]
fn outer_spec(x: i32) -> i32 {
    inner_spec(x)
}

fn main() {}
