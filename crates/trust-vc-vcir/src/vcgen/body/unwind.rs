// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unwind promises are obligations, not assumptions about input values.
use super::*;
use crate::UnwindSpec;

impl Gen<'_> {
    pub(super) fn check_unwind_call(
        &mut self,
        path: &Path,
        target: &FnDecl,
        actual: &Reads,
        call: (SpanId, SiteId),
        requires: Vec<(Source, Term)>,
    ) -> R<()> {
        if self.recommendations
            || matches!(self.decl.unwind_spec(), UnwindSpec::MayUnwind)
            || matches!(target.unwind_spec(), UnwindSpec::NoUnwind)
        {
            return Ok(());
        }
        let caller = match self.decl.unwind_spec() {
            UnwindSpec::MayUnwind => Term::Bool(false),
            UnwindSpec::NoUnwind => Term::Bool(true),
            UnwindSpec::NoUnwindWhen(condition) => {
                // `entry` is never the current mutable parameter environment.
                // Isolated loops already rebind and restore this same snapshot.
                let reads = Reads {
                    read: self.entry.clone(),
                    old: self.entry.clone(),
                    types: self.types.clone(),
                    ..Reads::default()
                };
                self.contract_term(&reads, condition)?
            }
        };
        if caller == Term::Bool(false) {
            return Ok(());
        }
        let callee = match target.unwind_spec() {
            UnwindSpec::NoUnwind => Term::Bool(true),
            UnwindSpec::MayUnwind => Term::Bool(false),
            UnwindSpec::NoUnwindWhen(condition) => self.contract_term(actual, condition)?,
        };
        if callee == Term::Bool(true) {
            return Ok(());
        }
        self.check(
            path,
            &[],
            Term::implies(caller, callee),
            call.1,
            CheckKind::Unwind {
                call: call.0,
                callee: target.id,
            },
            requires,
        )
    }
}
