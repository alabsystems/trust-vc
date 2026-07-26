// Test: spec function can call a later-defined spec function (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(unexpected_cfgs)]

#[trust_vc::spec]
fn outer_spec(x: i32) -> i32 {
    inner_spec(x)
}

#[trust_vc::spec]
fn inner_spec(x: i32) -> i32 {
    x + 1
}

fn main() {}
