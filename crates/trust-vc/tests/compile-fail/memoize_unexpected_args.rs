// Test: #[trust_vc::memoize] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::memoize(verbose)]
fn memoize_with_args() -> u64 {
    1
}

fn main() {}
