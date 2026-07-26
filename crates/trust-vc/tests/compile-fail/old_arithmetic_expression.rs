// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: ensures!(old!(a + b)) rejects arithmetic expressions instead of
// silently evaluating them in the post-state.

use trust_vc::ensures;

fn reject_arithmetic_expression(a: i32, b: i32) {
    ensures!(old!(a + b) == a + b);
}

fn main() {
    let _ = reject_arithmetic_expression as fn(i32, i32);
}
