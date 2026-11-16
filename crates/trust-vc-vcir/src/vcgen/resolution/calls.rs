// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Call argument transfers precede both normal and unwinding control flow.
use super::*;
use crate::FnId;

impl<'a> Builder<'a, '_> {
    pub(super) fn call(
        &mut self,
        statement: &'a Stmt,
        callee: FnId,
        args: &'a [Expr],
        dest: Option<&'a Place>,
        after: usize,
    ) -> R<usize> {
        let target = self
            .ctx
            .fns
            .get(&callee)
            .copied()
            .ok_or_else(|| refusal("resolution-call", "unknown call", statement.span))?;
        let mut events = Vec::new();
        for (argument, parameter) in args.iter().zip(&target.params) {
            if target
                .local(*parameter)
                .is_some_and(|local| local.mode != Mode::Spec)
            {
                events.extend(self.value_moves(argument)?);
            }
        }
        let key = Some(statement as *const Stmt as usize);
        let (result_events, result_dest) = match dest {
            Some(dest) => {
                self.charge(2 * (1 + dest.projections.len()))?;
                (vec![Event::Overwrite(dest.clone())], Some(dest.clone()))
            }
            None => (Vec::new(), None),
        };
        // statement() already registered this call's dedicated Action::None
        // after marker. It receives the POST-finalization state, before any
        // following statement or join; even a discarded result passes here.
        // The unwind edge never reaches it or restores captured ownership.
        let normal = self.node(
            None,
            result_events,
            Action::Result {
                call: statement as *const Stmt as usize,
                dest: result_dest,
            },
            vec![after],
        )?;
        if !matches!(target.unwind_spec(), crate::UnwindSpec::NoUnwind) {
            // MayUnwind and conditional contracts retain an unwind edge. A call
            // that unwinds transfers its arguments but never assigns its result.
            // Node zero has the function-exit boundary state: owned locals
            // may resolve, while values behind dereferences may live on.
            self.node(key, events, Action::Call(callee, args), vec![normal, 0])
        } else {
            self.node(key, events, Action::Call(callee, args), vec![normal])
        }
    }
}
