// Test: #[trust_vc::decreases] without a measure should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::decreases]
fn missing_decreases_measure(n: u64) -> u64 {
    if n == 0 { 1 } else { n * missing_decreases_measure(n - 1) }
}

fn main() {}
