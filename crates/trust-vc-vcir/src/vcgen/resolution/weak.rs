// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A possible overwrite joins old and new values without inventing a cover.
use super::*;

impl Builder<'_, '_> {
    pub(super) fn weak_aliases(
        &self,
        state: &mut OwnershipState,
        rows: &[(Place, Vec<Place>)],
        source: &Place,
        target: &Place,
    ) -> R<()> {
        self.invalidate_dependencies(state, target)?;
        let mut unknown = Vec::new();
        for (owner, old) in &mut state.aliases {
            self.charge(1 + owner.projections.len() + target.projections.len())?;
            if owner.local != target.local || !owner.projections.starts_with(&target.projections) {
                continue;
            }
            self.charge(1 + source.projections.len() + owner.projections.len())?;
            let mut input = source.clone();
            input
                .projections
                .extend_from_slice(&owner.projections[target.projections.len()..]);
            self.charge(rows.len().saturating_mul(1 + input.projections.len()))?;
            if let Some((_, new)) = rows.iter().find(|(place, _)| *place == input) {
                self.union(old, new)?;
            } else {
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

    pub(super) fn invalidate_dependencies(
        &self,
        state: &mut OwnershipState,
        place: &Place,
    ) -> R<()> {
        let mut unknown = Vec::new();
        for (owner, targets) in &state.aliases {
            let mut invalid = false;
            for target in targets {
                self.charge(
                    (1 + target.projections.len()).saturating_mul(1 + place.projections.len()),
                )?;
                if target.local != place.local {
                    continue;
                }
                for (index, projection) in target.projections.iter().enumerate() {
                    if *projection == Projection::Deref
                        && index >= place.projections.len()
                        && target.projections[..index].starts_with(&place.projections)
                        && !target.projections[place.projections.len()..index]
                            .contains(&Projection::Deref)
                    {
                        invalid = true;
                    }
                }
            }
            if invalid {
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
}
