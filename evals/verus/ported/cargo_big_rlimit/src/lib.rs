// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

use trust_vc_types::nat;

#[trust_vc::decreases(x)]
#[trust_vc::spec]
fn fib(x: nat) -> nat {
    if x == 0 {
        0
    } else if x == 1 {
        1
    } else {
        fib((x - 1) as nat) + fib((x - 2) as nat)
    }
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib() {
    trust_vc::assert_by_compute!(fib(26) == 121_393; compute_only);
}
