// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test: #[trust_vc::inline] and #[trust_vc::opaque] should be mutually exclusive.

#[trust_vc::spec]
#[trust_vc::inline]
#[trust_vc::opaque]
fn bad_spec(x: u64) -> u64 {
    x
}

fn main() {}
