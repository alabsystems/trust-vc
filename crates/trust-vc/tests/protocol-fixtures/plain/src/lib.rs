// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An action of `trust_vc_protocol_fixture_mc::Calm`, declared in a crate
//! built with neither `test` nor `trust_mc`.

use trust_vc_protocol_fixture_mc::Calm;

pub trait Jump {
    fn jump(&mut self);
}

impl Jump for Calm {
    #[trust_vc::action(Calm)]
    fn jump(&mut self) {
        self.x = 7;
    }
}
