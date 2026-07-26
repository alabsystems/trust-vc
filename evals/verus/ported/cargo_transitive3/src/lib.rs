// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib() {
    transitive2::test2();
    transitive2::b();
    trust_vc::assert!(true);
}
