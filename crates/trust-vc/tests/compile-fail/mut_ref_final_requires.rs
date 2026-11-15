// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc::requires;

fn reject_final_in_requires(x: &mut u64) {
    requires!(*final(x) == 5u64);
    *x = 5u64;
}

fn main() {
    let _ = reject_final_in_requires as fn(&mut u64);
}
