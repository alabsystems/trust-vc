// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dereference proxies never own the storage which survives their lifetime.
use super::*;
use std::collections::HashMap;

impl Builder<'_, '_> {
    pub(super) fn normalized(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        place: &Place,
    ) -> R<Vec<Place>> {
        self.normalize(aliases, place, &mut Vec::new())
    }
    fn normalize(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        place: &Place,
        active: &mut Vec<Place>,
    ) -> R<Vec<Place>> {
        self.work
            .places(std::slice::from_ref(place), self.decl.span)?;
        self.charge(active.len().saturating_mul(1 + place.projections.len()))?;
        if active.contains(place) {
            return Ok(vec![place.clone()]);
        }
        active.push(place.clone());
        let result = self.normalize_step(aliases, place, active);
        active.pop();
        result
    }
    fn normalize_step(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        place: &Place,
        active: &mut Vec<Place>,
    ) -> R<Vec<Place>> {
        for (index, projection) in place.projections.iter().enumerate() {
            self.charge(1 + index)?;
            if *projection != Projection::Deref {
                continue;
            }
            let prefix = Place {
                local: place.local,
                projections: place.projections[..index].to_vec(),
            };
            if let Some(targets) = aliases.get(&prefix) {
                let mut normalized = Vec::new();
                for target in targets {
                    self.charge(1 + target.projections.len() + place.projections.len())?;
                    let mut target = target.clone();
                    target
                        .projections
                        .extend_from_slice(&place.projections[index + 1..]);
                    let expanded = self.normalize(aliases, &target, active)?;
                    self.union(&mut normalized, &expanded)?;
                }
                if !normalized.is_empty() {
                    return Ok(normalized);
                }
            }
        }
        self.work
            .places(std::slice::from_ref(place), self.decl.span)?;
        Ok(vec![place.clone()])
    }

    pub(super) fn scope_drop(&self, state: &mut OwnershipState, locals: &[LocalId]) -> R<()> {
        let mut surviving = Vec::new();
        let mut surviving_aliases = Vec::new();
        for (owner, footprints) in &state.loans {
            self.charge(1 + locals.len() + owner.projections.len())?;
            if !locals.contains(&owner.local) || !owner.has_deref() {
                continue;
            }
            let targets = self.normalized(&state.aliases, owner)?;
            let mut unknown = false;
            for target in targets {
                self.charge(
                    (1 + state.initialized.len())
                        .saturating_mul(1 + target.projections.len())
                        .saturating_add(locals.len()),
                )?;
                if !state.is_initialized(&target)
                    || (locals.contains(&target.local) && target.has_deref())
                {
                    unknown = true;
                } else if !locals.contains(&target.local) {
                    self.work.places(footprints, self.decl.span)?;
                    surviving.push((target, footprints.clone()));
                }
            }
            if unknown {
                self.union(&mut state.escaped, footprints)?;
            }
        }
        for (owner, targets) in &state.aliases {
            self.charge(1 + locals.len() + owner.projections.len())?;
            if !locals.contains(&owner.local) || !owner.has_deref() {
                continue;
            }
            let destinations = self.normalized(&state.aliases, owner)?;
            let exact = destinations.len() == 1;
            for destination in destinations {
                self.charge(1 + locals.len())?;
                if !locals.contains(&destination.local) {
                    self.work.places(targets, self.decl.span)?;
                    surviving_aliases.push((destination, targets.clone(), exact));
                }
            }
        }
        self.charge(locals.len().saturating_mul(
            1 + state.declared.len()
                + state.represented.len()
                + state.initialized.len()
                + state.loans.len()
                + state.aliases.len()
                + state.moved.len(),
        ))?;
        state.declared.retain(|local| !locals.contains(local));
        state.represented.retain(|local| !locals.contains(local));
        state
            .initialized
            .retain(|place| !locals.contains(&place.local));
        state.moved.retain(|place| !locals.contains(&place.local));
        state
            .loans
            .retain(|place, _| !locals.contains(&place.local));
        state
            .aliases
            .retain(|place, _| !locals.contains(&place.local));
        for (owner, footprints) in surviving {
            self.union(state.loans.entry(owner).or_default(), &footprints)?;
        }
        for (owner, targets, exact) in surviving_aliases {
            if exact {
                self.union(state.aliases.entry(owner).or_default(), &targets)?;
            } else if let Some(known) = state.aliases.get_mut(&owner) {
                self.union(known, &targets)?;
            }
        }
        Ok(())
    }

    pub(super) fn preserve_overwrite(&self, state: &mut OwnershipState, place: &Place) -> R<()> {
        let mut surviving = Vec::new();
        let mut surviving_aliases = Vec::new();
        for (owner, footprints) in &state.loans {
            self.charge(1 + owner.projections.len() + place.projections.len())?;
            if owner.local != place.local
                || !owner.projections.starts_with(&place.projections)
                || !owner.projections[place.projections.len()..].contains(&Projection::Deref)
            {
                continue;
            }
            for target in self.normalized(&state.aliases, owner)? {
                self.charge(
                    (1 + state.initialized.len()).saturating_mul(1 + target.projections.len()),
                )?;
                let removed = target.local == place.local
                    && target.projections.starts_with(&place.projections);
                if !state.is_initialized(&target) || (removed && !covers(place, &target)) {
                    self.union(&mut state.escaped, footprints)?;
                } else if !removed {
                    self.work.places(footprints, self.decl.span)?;
                    surviving.push((target, footprints.clone()));
                }
            }
        }
        for (owner, targets) in &state.aliases {
            self.charge(1 + owner.projections.len() + place.projections.len())?;
            if owner.local != place.local
                || !owner.projections.starts_with(&place.projections)
                || !owner.projections[place.projections.len()..].contains(&Projection::Deref)
            {
                continue;
            }
            let destinations = self.normalized(&state.aliases, owner)?;
            let exact = destinations.len() == 1;
            for destination in destinations {
                self.charge(1 + destination.projections.len())?;
                if destination.local != place.local
                    || !destination.projections.starts_with(&place.projections)
                {
                    self.work.places(targets, self.decl.span)?;
                    surviving_aliases.push((destination, targets.clone(), exact));
                }
            }
        }
        for (owner, footprints) in surviving {
            self.union(state.loans.entry(owner).or_default(), &footprints)?;
        }
        for (owner, targets, exact) in surviving_aliases {
            if exact {
                self.union(state.aliases.entry(owner).or_default(), &targets)?;
            } else if let Some(known) = state.aliases.get_mut(&owner) {
                self.union(known, &targets)?;
            }
        }
        Ok(())
    }

    pub(super) fn install(
        &self,
        relation: &mut HashMap<Place, Vec<Place>>,
        rows: &[(Place, Vec<Place>)],
        source: &Place,
        targets: &[Place],
    ) -> R<()> {
        for target in targets {
            for (owner, values) in rows {
                self.charge(
                    1 + owner.projections.len()
                        + source.projections.len()
                        + target.projections.len(),
                )?;
                if owner.local == source.local && owner.projections.starts_with(&source.projections)
                {
                    let mut mapped = target.clone();
                    mapped
                        .projections
                        .extend_from_slice(&owner.projections[source.projections.len()..]);
                    self.union(relation.entry(mapped).or_default(), values)?;
                }
            }
        }
        Ok(())
    }
}
