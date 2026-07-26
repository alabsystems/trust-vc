// Test: #[trust_vc::returns] is invalid on a spec function when returns is outermost.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::returns(result)]
#[trust_vc::spec]
fn spec_with_returns_outer(x: u8) -> bool {
    x == 3
}

fn main() {}
