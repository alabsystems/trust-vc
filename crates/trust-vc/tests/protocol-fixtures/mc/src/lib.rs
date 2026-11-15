// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Protocols whose components are declared here and, for `Calm`, in another
//! crate (`trust-vc-protocol-fixture-plain`). Each counts `x` to 1 through
//! `settle` and checks `small == x < 5`.

/// `jump`, declared in `trust-vc-protocol-fixture-plain`, sets `x` to 7.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Calm {
    pub x: u8,
}

impl Calm {
    #[trust_vc::action(Calm)]
    pub fn settle(&mut self) {
        self.x = 1;
    }

    #[trust_vc::safety(Calm)]
    pub fn small(&self) -> bool {
        self.x < 5
    }
}

/// The control: `jump` is declared in this crate.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Gate {
    pub x: u8,
}

impl Gate {
    #[trust_vc::action(Gate)]
    pub fn settle(&mut self) {
        self.x = 1;
    }

    #[trust_vc::action(Gate)]
    pub fn jump(&mut self) {
        self.x = 7;
    }

    #[trust_vc::safety(Gate)]
    pub fn small(&self) -> bool {
        self.x < 5
    }
}

/// The twin: no `jump` anywhere.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Still {
    pub x: u8,
}

impl Still {
    #[trust_vc::action(Still)]
    pub fn settle(&mut self) {
        self.x = 1;
    }

    #[trust_vc::safety(Still)]
    pub fn small(&self) -> bool {
        self.x < 5
    }
}
