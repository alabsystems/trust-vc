// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub fn test2() {
    let _ok = transitive1::test1();
    trust_vc::assert!(true);
}

pub fn b() {
    transitive1::c();
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib() {
    test2();
    b();
    trust_vc::assert!(true);
}
