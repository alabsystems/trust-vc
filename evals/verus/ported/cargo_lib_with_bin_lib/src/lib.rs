// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(ensures(result == (x as u32) + (x as u32)), returns(result))]
pub fn lib(x: u16) -> u32 {
    x as u32 + x as u32
}

pub use lib as double;
