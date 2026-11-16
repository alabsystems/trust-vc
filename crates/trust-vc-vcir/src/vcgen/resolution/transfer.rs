// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordered ownership effects of one CFG node.
use super::*;

impl Builder<'_, '_> {
    pub(super) fn transfer(
        &self,
        state: &mut OwnershipState,
        index: usize,
        universe: &[Place],
        refs: &[Place],
    ) -> R<()> {
        let action = &self.nodes[index].action;
        let mut result = match action {
            Action::Result { call, dest } => self.finish_call(state, *call, dest.as_ref())?,
            _ => CallOutput::default(),
        };
        let saved = match action {
            Action::Result { .. } => std::mem::take(&mut result.loans),
            Action::Declare(local, Some(value))
                if self
                    .decl
                    .local(*local)
                    .is_some_and(|local| local.mode != Mode::Spec) =>
            {
                self.value_provenance(state, value, &Place::local(*local), refs)?
            }
            Action::Assign(place, value) if self.kept_place(place)? => {
                self.value_provenance(state, value, place, refs)?
            }
            _ => Vec::new(),
        };
        let mut aliases = match action {
            Action::Result { .. } => std::mem::take(&mut result.aliases),
            Action::Declare(local, Some(value))
                if self
                    .decl
                    .local(*local)
                    .is_some_and(|local| local.mode != Mode::Spec) =>
            {
                self.value_aliases(state, value, &Place::local(*local), refs)?
            }
            Action::Assign(place, value) if self.kept_place(place)? => {
                self.value_aliases(state, value, place, refs)?
            }
            _ => Vec::new(),
        };
        let destinations = match action {
            Action::Assign(place, _)
            | Action::Result {
                dest: Some(place), ..
            } => {
                Some(self.possible_targets(&state.aliases, &state.loans, &state.escaped, place)?)
            }
            _ => None,
        };
        if let Action::Result {
            dest: Some(dest), ..
        } = action
        {
            if let Some((writes, _)) = &destinations {
                self.stable_result_aliases(state, &mut aliases, dest, writes)?;
            }
        }
        let borrowed = match action {
            Action::Borrow(_, place) => Some(self.borrowed(state, place)?),
            _ => None,
        };
        let contents = match action {
            Action::Borrow(dest, place) => Some(self.borrow_contents(state, place, *dest)?),
            _ => None,
        };
        if let Action::Call(callee, args) = action {
            let call = self.nodes[index].statement.ok_or_else(|| {
                refusal(
                    "resolution-call",
                    "call capture has no original statement",
                    self.decl.span,
                )
            })?;
            self.capture_call(state, call, *callee, args, refs)?;
        }
        if let Action::Return(Some(value)) = action {
            if self
                .decl
                .local(self.decl.ret)
                .is_some_and(|local| local.mode != Mode::Spec)
            {
                for (_, footprints) in
                    self.value_provenance(state, value, &Place::local(self.decl.ret), refs)?
                {
                    self.union(&mut state.escaped, &footprints)?;
                }
            }
        }
        for event in &self.nodes[index].events {
            if let Event::Move(place) = event {
                self.moved(state, place, refs)?;
            }
        }
        match action {
            Action::Declare(local, init) => {
                self.charge(1 + state.declared.len())?;
                if !state.declared.contains(local) {
                    state.declared.push(*local);
                }
                let declaration = self.decl.local(*local).ok_or_else(|| {
                    refusal("resolution-type", "unknown declared local", self.decl.span)
                })?;
                self.charge(universe.len())?;
                let represented = init.is_some()
                    || !self
                        .ctx
                        .shape(&declaration.ty, Some(self.decl.id), self.decl.span)?
                        .has_poly();
                if represented && !state.represented.contains(local) {
                    state.represented.push(*local);
                }
                self.write(state, &Place::local(*local), init.is_some(), universe)?;
            }
            Action::Assign(place, _)
            | Action::Result {
                dest: Some(place), ..
            } => {
                self.write(state, place, true, universe)?;
                if let Some((targets, complete)) = &destinations {
                    let exact = *complete && targets.len() == 1;
                    if exact && targets[0] != *place {
                        self.write(state, &targets[0], true, universe)?;
                    }
                    if !exact {
                        for target in targets {
                            self.charge(1 + target.projections.len() + place.projections.len())?;
                            if target != place {
                                self.preserve_overwrite(state, target)?;
                                self.weak_aliases(state, &aliases, place, target)?;
                            }
                        }
                    }
                    self.install(&mut state.loans, &saved, place, targets)?;
                    if exact {
                        self.install(&mut state.aliases, &aliases, place, targets)?;
                    }
                }
                if place.projections.is_empty() && !state.represented.contains(&place.local) {
                    state.represented.push(place.local);
                }
            }
            Action::Borrow(dest, place) => {
                let targets = self.normalized(&state.aliases, place)?;
                let target = Place::local(*dest);
                self.write(state, &target, true, universe)?;
                self.charge(1 + state.represented.len())?;
                if !state.represented.contains(dest) {
                    state.represented.push(*dest);
                }
                if let Some(footprints) = borrowed {
                    state.loans.insert(target, footprints);
                }
                state.aliases.insert(Place::local(*dest), targets);
                if let Some((loans, aliases)) = contents {
                    for (owner, footprints) in loans {
                        state.loans.insert(owner, footprints);
                    }
                    for (owner, targets) in aliases {
                        state.aliases.insert(owner, targets);
                    }
                }
            }
            Action::Drop(locals) => self.scope_drop(state, locals)?,
            _ => {}
        }
        for (owner, footprints) in saved {
            state.loans.insert(owner, footprints);
        }
        for (owner, targets) in aliases {
            state.aliases.insert(owner, targets);
        }
        Ok(())
    }

    fn moved(&self, state: &mut OwnershipState, place: &Place, refs: &[Place]) -> R<()> {
        let (mut targets, _) =
            self.possible_targets(&state.aliases, &state.loans, &state.escaped, place)?;
        self.union(&mut targets, std::slice::from_ref(place))?;
        for target in targets {
            self.moved_one(state, &target, refs)?;
        }
        Ok(())
    }

    fn moved_one(&self, state: &mut OwnershipState, place: &Place, refs: &[Place]) -> R<()> {
        self.invalidate_dependencies(state, place)?;
        self.charge(
            (state.initialized.len() + state.loans.len() + state.aliases.len())
                .saturating_mul(1 + place.projections.len()),
        )?;
        state.initialized.retain(|old| {
            !(covers(old, place)
                || (old.local == place.local && old.projections.starts_with(&place.projections)))
        });
        state.loans.retain(|owner, _| {
            !(owner.local == place.local && owner.projections.starts_with(&place.projections))
        });
        state.aliases.retain(|owner, _| {
            !(owner.local == place.local && owner.projections.starts_with(&place.projections))
        });
        let mut found = false;
        for carrier in refs {
            self.charge(1 + carrier.projections.len() + place.projections.len())?;
            if covers(place, carrier) {
                self.union(&mut state.moved, std::slice::from_ref(carrier))?;
                found = true;
            }
        }
        if !found {
            self.union(&mut state.moved, std::slice::from_ref(place))?;
        }
        Ok(())
    }

    fn write(
        &self,
        state: &mut OwnershipState,
        place: &Place,
        initialized: bool,
        universe: &[Place],
    ) -> R<()> {
        self.preserve_overwrite(state, place)?;
        self.invalidate_dependencies(state, place)?;
        self.charge(
            (state.initialized.len() + state.moved.len() + state.loans.len() + state.aliases.len())
                .saturating_mul(1 + place.projections.len()),
        )?;
        state.initialized.retain(|old| {
            !(old.local == place.local && old.projections.starts_with(&place.projections))
        });
        state.loans.retain(|owner, _| {
            !(owner.local == place.local && owner.projections.starts_with(&place.projections))
        });
        state.aliases.retain(|owner, _| {
            !(owner.local == place.local && owner.projections.starts_with(&place.projections))
        });
        state.moved.retain(|old| !covers(place, old));
        if initialized {
            for candidate in universe {
                self.charge(
                    (1 + state.initialized.len()).saturating_mul(1 + candidate.projections.len()),
                )?;
                if candidate.local == place.local
                    && candidate.projections.starts_with(&place.projections)
                    && !state.initialized.contains(candidate)
                {
                    self.work
                        .places(std::slice::from_ref(candidate), self.decl.span)?;
                    state.initialized.push(candidate.clone());
                }
            }
        }
        self.reconstruct_initialized(state, universe)
    }
}
