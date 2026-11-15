// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn reject_final_in_assert(x: &mut u64) {
    *x = 5u64;
    trust_vc::assert!(*final(x) == 5u64);
}

fn main() {
    let _ = reject_final_in_assert as fn(&mut u64);
}
