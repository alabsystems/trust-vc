// Test: proof function can call a later-defined proof function (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(unexpected_cfgs)]

#[trust_vc::proof]
fn outer_proof(x: i32) {
    inner_proof(x);
}

#[trust_vc::proof]
fn inner_proof(x: i32) {
    let _ = x + 1;
}

fn main() {}
