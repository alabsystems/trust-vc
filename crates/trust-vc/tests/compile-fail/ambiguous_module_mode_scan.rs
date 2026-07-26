// Test: ambiguous same-name inline modules must fail closed in mode_scan (#2300).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(unexpected_cfgs)]

mod alpha {
    fn outer() {
        inner();
    }

    fn inner() {}
}

mod beta {
    use trust_vc::proof;

    #[proof]
    fn outer() {
        inner();
    }

    #[proof]
    fn inner() {}
}

fn main() {}
