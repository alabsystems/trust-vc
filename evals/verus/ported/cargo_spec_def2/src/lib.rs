// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::int;

#[trust_vc::spec]
pub fn double(x: u16) -> int {
    (x as int) + (x as int) + 1i128
}

#[trust_vc::contract(
    requires(double(x) < 100i128),
    ensures(result == x),
    returns(result),
)]
pub fn lib(x: u16) -> u16 {
    x
}

pub use lib as concrete_a;
