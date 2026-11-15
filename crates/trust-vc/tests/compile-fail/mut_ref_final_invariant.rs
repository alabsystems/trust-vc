// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn reject_final_in_invariant(x: &mut u64) {
    let mut i = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(*final(x) == 5u64);
        i = i + 1u64;
    }
}

fn main() {
    let _ = reject_final_in_invariant as fn(&mut u64);
}
