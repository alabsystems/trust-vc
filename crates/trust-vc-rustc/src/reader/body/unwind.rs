//! Native unwind headers remain typed contracts through lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl FnReader<'_, '_> {
    pub(super) fn unwind_rules(&mut self) {
        if self.unwind.is_some() && self.mode != Mode::Exec {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                "an 'unwind' specification can only be given on exec functions",
            ));
        }
    }
}
