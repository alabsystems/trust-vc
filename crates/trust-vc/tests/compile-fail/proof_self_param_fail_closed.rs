// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: `#[trust_vc::proof]` methods with `self` fail closed instead of
// silently skipping receiver registration.

struct ProofHost1753;

impl ProofHost1753 {
    #[trust_vc::proof]
    fn unsupported_self_1753(&self, x: i32) {
        let _ = x;
    }
}

fn main() {}
