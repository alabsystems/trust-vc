// Test: #[trust_vc::returns] is invalid on a spec function when spec is outermost.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::spec]
#[trust_vc::returns(result)]
fn spec_with_inner_returns(x: u8) -> bool {
    x == 3
}

fn main() {}
