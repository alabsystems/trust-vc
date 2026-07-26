// Test: proof function calling spec function via crate:: is legal (#2066).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(unused_braces)]

mod specs {
    #[trust_vc::spec]
    pub fn helper(x: i32) -> i32 {
        x + 1
    }
}

#[trust_vc::proof]
fn legal(x: i32) {
    let _ = crate::specs::helper(x);
}

fn main() {}
