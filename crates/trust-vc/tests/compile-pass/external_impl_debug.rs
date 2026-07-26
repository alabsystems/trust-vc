// Test: #[trust_vc::external] accepts trusted impl blocks.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(warnings)]

struct CustomErr {
    error_code: i32,
}

#[trust_vc::external]
impl core::fmt::Debug for CustomErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CustomErr({})", self.error_code)
    }
}

fn main() {
    let rendered = format!("{:?}", CustomErr { error_code: -1 });
    assert_eq!(rendered, "CustomErr(-1)");
}
