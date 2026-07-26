// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[derive(Debug, Copy, Clone, PartialEq)]
struct A(u8);

#[trust_vc::contract(ensures(true), returns(result))]
fn main() {
    let _a = A(5);
    trust_vc::assert!(1u8 == 0u8 + 1u8);
}
