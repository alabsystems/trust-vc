// Test: #[trust_vc::trigger] without a pattern should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::broadcast]
#[trust_vc::trigger]
fn missing_trigger_pattern(n: u64) {
    trust_vc::ensures!(n >= 0);
}

fn main() {}
