// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub fn test_calling(x: u16) {
    use spec_use::*;

    let y = concrete_b(x);
    let z = concrete_caller(y);
    println!("{}", z);
}

#[trust_vc::contract(
    requires(x < 50u16),
    ensures(result == x),
    returns(result),
)]
pub fn direct_body_call(x: u16) -> u16 {
    let y = spec_use::concrete_b(x);
    spec_use::concrete_caller(y)
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib(x: u16) {
    test_calling(x);
}
