// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub fn foo(x: u64, y: u64, z: u64) {
    let _ = vstd_macro_usage::do_something(x, y, z);
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib(x: u64, y: u64, z: u64) {
    foo(x, y, z);
    trust_vc::assert!(true);
}
