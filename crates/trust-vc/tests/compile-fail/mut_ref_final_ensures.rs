// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// The reserved-keyword spec op `final(..)` PARSES, so without
// the refusal this expands `__trust_vc_mut_ref_final(x)` into the runtime
// assertion and rustc reports E0425 on a symbol the author never wrote.

use trust_vc::ensures;

fn reject_final_in_ensures(x: &mut u64) {
    ensures!(*final(x) == 5u64);
    *x = 5u64;
}

fn main() {
    let _ = reject_final_in_ensures as fn(&mut u64);
}
