// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: recursive proof functions must declare #[trust_vc::decreases(...)].

#[trust_vc::proof]
fn bad_lemma(n: u64) {
    if n > 0 {
        bad_lemma(n - 1);
    }
}

fn main() {}
