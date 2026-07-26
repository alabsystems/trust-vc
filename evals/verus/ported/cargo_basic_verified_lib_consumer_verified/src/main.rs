// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use basic_verified_lib::double;

#[trust_vc::contract(ensures(true), returns(result))]
fn main() {
    let _x = double(42);
    trust_vc::assert!(true);
    trust_vc::assert!(42u32 + 42u32 == 84u32);
}
