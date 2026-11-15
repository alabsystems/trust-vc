// Test: a protocol component must be a method of the protocol it names
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// `Narrow::step` overflows its `u8` at 200 + 100. Registered as an action of
// `Counter`, its `self.x` was modelled as `Counter::x`, a `u64`, and the
// protocol verified.
#[trust_vc::protocol]
pub struct Counter {
    pub x: u64,
}

pub struct Narrow {
    pub x: u8,
}

impl Narrow {
    #[trust_vc::action(Counter)]
    pub fn step(&mut self) {
        self.x = self.x + 100;
    }
}

fn main() {}
