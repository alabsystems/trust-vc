// Test: #[trust_vc::returns] without a name should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::returns]
fn missing_name() -> i32 {
    42
}

fn main() {}
