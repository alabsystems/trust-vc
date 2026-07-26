//! Native Seq helpers shared with String/StrSlice shadow views.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use super::super::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    pub(super) fn resolve_native_seq_receiver(&self, receiver: Term) -> Term {
        self.lookup_native_seq_shadow(receiver)
            .map(|shadow| shadow.native_term)
            .unwrap_or(receiver)
    }
}
