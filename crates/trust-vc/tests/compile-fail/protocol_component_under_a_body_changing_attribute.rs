// Test: a protocol component carries no attribute that could change its body
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// `#[trust_vc::action]` reads `bump`'s body as written; the attribute macro
// below it runs after and adds a runtime `assert!(self.x < 5)` in a non-test
// build. The model's `bump` never panics, while the Rust `bump` panics after
// `jump`, and the protocol verified.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Capped {
    pub x: u8,
}

impl Capped {
    #[trust_vc::action(Capped)]
    pub fn jump(&mut self) {
        self.x = 9;
    }

    #[trust_vc::action(Capped)]
    #[trust_vc::contract(requires(self.x < 5))]
    pub fn bump(&mut self) {
        self.x = 1;
    }
}

fn main() {}
