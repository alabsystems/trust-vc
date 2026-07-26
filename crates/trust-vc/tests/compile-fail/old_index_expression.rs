// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: ensures!(old!(arr[i])) rejects index expressions instead of silently
// evaluating them in the post-state.

use trust_vc::ensures;

fn reject_index_expression(arr: [i32; 3], i: usize) {
    ensures!(arr[i] == old!(arr[i]));
}

fn main() {
    let _ = reject_index_expression as fn([i32; 3], usize);
}
