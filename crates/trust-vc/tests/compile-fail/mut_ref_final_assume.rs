// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn reject_final_in_assume(x: &mut u64) {
    trust_vc::assume!(*final(x) == 5u64);
}

fn main() {
    let _ = reject_final_in_assume as fn(&mut u64);
}
