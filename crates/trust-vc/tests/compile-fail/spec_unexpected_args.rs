// Test: #[trust_vc::spec] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::spec(verbose)]
fn spec_with_args() -> bool {
    true
}

fn main() {}
