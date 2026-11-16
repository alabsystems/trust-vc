// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Definite initialization and possible place-based loans share the CFG.
use super::*;
use std::collections::VecDeque;

impl Builder<'_, '_> {
    pub(super) fn forward(
        &self,
        entry: usize,
        universe: &[Place],
        refs: &[Place],
        resolved: &[Vec<bool>],
    ) -> R<Vec<Option<OwnershipState>>> {
        self.charge(self.nodes.len())?;
        let mut states = vec![None; self.nodes.len()];
        let mut initial = OwnershipState::default();
        self.charge(self.decl.params.len() * 2 + universe.len())?;
        initial.declared.extend(&self.decl.params);
        initial.represented.extend(&self.decl.params);
        for place in universe {
            self.charge(1 + self.decl.params.len())?;
            if self.decl.params.contains(&place.local) {
                self.work
                    .places(std::slice::from_ref(place), self.decl.span)?;
                initial.initialized.push(place.clone());
            }
        }
        states[entry] = Some(initial);
        let mut pending = VecDeque::from([entry]);
        let mut queued = vec![false; self.nodes.len()];
        queued[entry] = true;
        while let Some(index) = pending.pop_front() {
            queued[index] = false;
            let Some(state) = &states[index] else {
                continue;
            };
            let mut output = state.copy(&self.work, self.decl.span)?;
            for (place, yes) in refs.iter().zip(&resolved[index]) {
                self.charge(
                    (1 + output.initialized.len()).saturating_mul(1 + place.projections.len()),
                )?;
                if *yes && output.is_initialized(place) {
                    output.loans.remove(place);
                }
            }
            self.transfer(&mut output, index, universe, refs)?;
            self.quarantine(&mut output)?;
            for next in &self.nodes[index].next {
                self.charge(1)?;
                let changed = match &mut states[*next] {
                    None => {
                        states[*next] = Some(output.copy(&self.work, self.decl.span)?);
                        true
                    }
                    Some(previous) => self.join(previous, &output)?,
                };
                if changed && !queued[*next] {
                    queued[*next] = true;
                    pending.push_back(*next);
                }
            }
        }
        Ok(states)
    }

    fn join(&self, previous: &mut OwnershipState, incoming: &OwnershipState) -> R<bool> {
        previous.price(&self.work, self.decl.span)?;
        incoming.price(&self.work, self.decl.span)?;
        let old = previous.copy(&self.work, self.decl.span)?;
        self.charge(
            previous
                .declared
                .len()
                .saturating_mul(1 + incoming.declared.len()),
        )?;
        previous
            .declared
            .retain(|local| incoming.declared.contains(local));
        self.charge(
            previous
                .represented
                .len()
                .saturating_mul(1 + incoming.represented.len()),
        )?;
        previous
            .represented
            .retain(|local| incoming.represented.contains(local));
        for place in &previous.initialized {
            self.charge(
                (1 + incoming.initialized.len()).saturating_mul(1 + place.projections.len()),
            )?;
        }
        previous
            .initialized
            .retain(|place| incoming.initialized.contains(place));
        self.union(&mut previous.moved, &incoming.moved)?;
        self.union(&mut previous.escaped, &incoming.escaped)?;
        for (owner, footprints) in &incoming.loans {
            self.work
                .places(std::slice::from_ref(owner), self.decl.span)?;
            self.union(previous.loans.entry(owner.clone()).or_default(), footprints)?;
        }
        let mut unknown = Vec::new();
        for (owner, targets) in &mut previous.aliases {
            self.work
                .places(std::slice::from_ref(owner), self.decl.span)?;
            if let Some(other) = incoming.aliases.get(owner) {
                self.union(targets, other)?;
            } else {
                unknown.push(owner.clone());
            }
        }
        for owner in unknown {
            previous.aliases.remove(&owner);
        }
        self.quarantine(previous)?;
        self.join_pending(&mut previous.pending_call, &incoming.pending_call)?;
        previous.price(&self.work, self.decl.span)?;
        old.price(&self.work, self.decl.span)?;
        Ok(*previous != old)
    }

    fn quarantine(&self, state: &mut OwnershipState) -> R<()> {
        let mut absent = Vec::new();
        for (owner, footprints) in &state.loans {
            self.charge((1 + state.initialized.len()).saturating_mul(1 + owner.projections.len()))?;
            if !state.is_initialized(owner) {
                self.work
                    .places(std::slice::from_ref(owner), self.decl.span)?;
                absent.push(owner.clone());
                self.union(&mut state.escaped, footprints)?;
            }
        }
        for owner in absent {
            state.loans.remove(&owner);
        }
        let mut unknown = Vec::new();
        for owner in state.aliases.keys() {
            self.charge((1 + state.initialized.len()).saturating_mul(1 + owner.projections.len()))?;
            if !state.is_initialized(owner) {
                self.work
                    .places(std::slice::from_ref(owner), self.decl.span)?;
                unknown.push(owner.clone());
            }
        }
        for owner in unknown {
            state.aliases.remove(&owner);
        }
        Ok(())
    }

    pub(super) fn union(&self, target: &mut Vec<Place>, source: &[Place]) -> R<()> {
        for place in source {
            self.charge(
                target
                    .len()
                    .saturating_mul(1 + place.projections.len())
                    .saturating_add(1),
            )?;
            if let Err(position) = target.binary_search_by(|old| state::place_order(old, place)) {
                self.work
                    .places(std::slice::from_ref(place), self.decl.span)?;
                target.insert(position, place.clone());
            }
        }
        Ok(())
    }
}
