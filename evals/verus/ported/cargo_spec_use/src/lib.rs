// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(
    requires(spec_def::double(x) < 100i128),
    ensures(result == x),
    returns(result),
)]
pub fn concrete_b(x: u16) -> u16 {
    x
}

#[trust_vc::contract(
    requires(spec_def::double(x) < 100i128),
    ensures(result == x),
    returns(result),
)]
pub fn concrete_caller(x: u16) -> u16 {
    spec_def::concrete_a(x)
}

#[trust_vc::contract(
    ensures(spec_def::double(x) == spec_def2::double(x) - 1i128),
    returns(result),
)]
pub fn test(x: u16) -> bool {
    true
}

#[trust_vc::contract(
    requires(spec_def::double(x) < 100i128),
    ensures(result == x),
    returns(result),
)]
pub fn lib(x: u16) -> u16 {
    concrete_caller(x)
}
