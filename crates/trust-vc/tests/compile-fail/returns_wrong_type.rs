// Test: Verus-style return-postcondition expression with wrong type should error.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::returns(20u8)]
fn wrong_type() -> bool {
    true
}

fn main() {}
