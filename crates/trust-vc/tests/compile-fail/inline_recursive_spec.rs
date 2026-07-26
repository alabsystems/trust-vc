// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test: #[trust_vc::inline] should reject recursive spec functions.

#[trust_vc::spec]
#[trust_vc::inline]
fn count_down(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        count_down(n - 1) + 1
    }
}

fn main() {}
