// Test: #[trust_vc::returns(expr)] fails closed on macro-hidden returns.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

macro_rules! early {
    ($e:expr) => {
        $e
    };
}

#[trust_vc::returns(20u8)]
fn hidden_return() -> u8 {
    early!(return 20u8);
    20u8
}

fn main() {}
