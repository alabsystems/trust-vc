// Test: proof function calling exec function via crate:: should fail mode checking (#2066).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod runtime {
    pub fn touch(x: i32) -> i32 { x }
}

#[trust_vc::proof]
fn illegal(x: i32) {
    crate::runtime::touch(x);
}

fn main() {}
