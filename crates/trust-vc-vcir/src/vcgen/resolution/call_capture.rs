// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Freeze argument origins before either call successor consumes them.
use super::*;
use crate::FnId;

impl Builder<'_, '_> {
    pub(super) fn capture_call(
        &self,
        state: &mut OwnershipState,
        call: usize,
        callee: FnId,
        args: &[Expr],
        refs: &[Place],
    ) -> R<()> {
        let target = self
            .ctx
            .fns
            .get(&callee)
            .copied()
            .ok_or_else(|| refusal("resolution-call", "unknown call", self.decl.span))?;
        let summary = super::super::call_identity::derive(
            target,
            self.ctx,
            self.work.remaining(),
            self.decl.span,
        )?;
        self.work.places(&state.escaped, self.decl.span)?;
        let escaped_before = state.escaped.clone();
        let mut bindings = Vec::new();
        for binding in summary.bindings {
            self.charge(1)?;
            bindings.push(ReturnBinding {
                result: binding.result,
                parameter: binding.parameter,
                argument: binding.argument,
            });
        }
        let mut arguments = Vec::new();
        for (parameter, (argument, formal)) in args.iter().zip(&target.params).enumerate() {
            if target
                .local(*formal)
                .is_some_and(|local| local.mode != Mode::Spec)
            {
                self.charge(1)?;
                arguments.push(self.capture_argument(state, parameter, *formal, argument, refs)?);
            }
        }
        let pending = PendingCall {
            call,
            escaped_before,
            bindings,
            arguments,
        };
        for argument in &pending.arguments {
            for row in &argument.rows {
                self.union(&mut state.escaped, &row.loans)?;
            }
            for origin in &argument.extras {
                self.union(&mut state.escaped, &origin.loans)?;
            }
        }
        state.pending_call = Some(pending);
        Ok(())
    }

    fn capture_argument(
        &self,
        state: &OwnershipState,
        parameter: usize,
        formal: LocalId,
        value: &Expr,
        refs: &[Place],
    ) -> R<CapturedArgument> {
        let loans = self.value_provenance(state, value, &Place::local(formal), refs)?;
        let aliases = self.value_aliases(state, value, &Place::local(formal), refs)?;
        let slots = super::super::call_identity::owned_slots(
            self.ctx,
            &value.ty,
            self.work.remaining(),
            value.span,
        )?;
        let mut keys = Vec::new();
        for (owner, _) in loans.iter().chain(&aliases) {
            self.union(&mut keys, std::slice::from_ref(owner))?;
        }
        let mut rows = Vec::new();
        let mut selected = Vec::new();
        for owner in keys {
            self.charge((loans.len() + aliases.len()).saturating_mul(1 + owner.projections.len()))?;
            let footprints = match loans.iter().find(|(place, _)| *place == owner) {
                Some((_, footprints)) => {
                    self.work.places(footprints, value.span)?;
                    footprints.clone()
                }
                None => Vec::new(),
            };
            let cover = match aliases.iter().find(|(place, _)| *place == owner) {
                Some((_, targets)) => self.freeze_aliases(state, targets)?,
                None => None,
            };
            let source = self.argument_source(value, &owner.projections)?;
            if let Some(source) = &source {
                let (mut origins, _) =
                    self.possible_targets(&state.aliases, &state.loans, &state.escaped, source)?;
                self.union(&mut origins, std::slice::from_ref(source))?;
                self.union(&mut selected, &origins)?;
            }
            let survivors = self.surviving_storage(state, value, &owner.projections, &slots)?;
            self.charge(1)?;
            rows.push(CapturedRow {
                path: owner.projections,
                source,
                loans: footprints,
                aliases: cover,
                survivors,
            });
        }
        let extras = self.extra_origins(state, value, &selected)?;
        Ok(CapturedArgument {
            parameter,
            rows,
            extras,
        })
    }

    fn freeze_aliases(&self, state: &OwnershipState, targets: &[Place]) -> R<Option<Vec<Place>>> {
        let mut stable = Vec::new();
        for target in targets {
            let (locations, complete) =
                self.possible_targets(&state.aliases, &state.loans, &state.escaped, target)?;
            if !complete {
                return Ok(None);
            }
            self.union(&mut stable, &locations)?;
        }
        Ok(Some(stable))
    }

    fn surviving_storage(
        &self,
        state: &OwnershipState,
        value: &Expr,
        path: &[Projection],
        slots: &[Vec<Projection>],
    ) -> R<Option<Vec<Place>>> {
        for slot in slots {
            self.charge(1 + slot.len() + path.len())?;
            if !path.starts_with(slot) {
                continue;
            }
            let Some(mut source) = self.argument_source(value, slot)? else {
                return Ok(None);
            };
            self.charge(path.len())?;
            source.projections.extend_from_slice(&path[slot.len()..]);
            let (locations, complete) =
                self.possible_targets(&state.aliases, &state.loans, &state.escaped, &source)?;
            return Ok(complete.then_some(locations));
        }
        Ok(None)
    }
}
