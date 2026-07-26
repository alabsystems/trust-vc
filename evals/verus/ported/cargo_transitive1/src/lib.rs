// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub fn test1() -> bool {
    true
}

pub fn c() {}

#[trust_vc::contract(ensures(result), returns(result))]
pub fn lib() -> bool {
    true
}
