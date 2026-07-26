// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use lib_with_bin::double;

#[trust_vc::contract(ensures(true), returns(result))]
fn main() {
    let _result = double(21);
    trust_vc::assert!(true);
    trust_vc::assert!(21u32 + 21u32 == 42u32);
}
