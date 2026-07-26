// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: `#[trust_vc::broadcast]` tuple-destructured parameters fail closed
// instead of silently skipping variable registration.

#[trust_vc::broadcast]
fn unsupported_tuple_1753((a, b): (i32, i32)) {
    let _ = (a, b);
}

fn main() {}
