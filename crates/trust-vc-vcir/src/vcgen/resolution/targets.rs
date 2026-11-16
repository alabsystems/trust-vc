// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Separate complete target covers from conservative possible write targets.
use super::*;
use std::collections::HashMap;

impl Builder<'_, '_> {
    pub(super) fn possible_targets(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        loans: &HashMap<Place, Vec<Place>>,
        escaped: &[Place],
        place: &Place,
    ) -> R<(Vec<Place>, bool)> {
        let mut targets = self.normalized(aliases, place)?;
        let complete = self.target_cover(aliases, place, &mut Vec::new())?;
        if complete {
            return Ok((targets, true));
        }
        // Unknown does not erase the known local alternatives carried by a
        // borrow. Footprints are used only for weak metadata updates here;
        // they grant neither initialization nor value equations.
        for (index, projection) in place.projections.iter().enumerate() {
            self.charge(1 + index)?;
            if *projection != Projection::Deref {
                continue;
            }
            let prefix = Place {
                local: place.local,
                projections: place.projections[..index].to_vec(),
            };
            let Some(Ty::MutRef(inner)) = self.typed_place(&prefix)? else {
                continue;
            };
            let local = loans.get(&prefix).map_or(&[][..], Vec::as_slice);
            for footprint in local.iter().chain(escaped) {
                self.charge(1 + footprint.projections.len() + place.projections.len())?;
                if self.typed_place(footprint)?.as_ref() != Some(inner.as_ref()) {
                    continue;
                }
                let mut candidate = footprint.clone();
                candidate
                    .projections
                    .extend_from_slice(&place.projections[index + 1..]);
                let expanded = self.normalized(aliases, &candidate)?;
                self.union(&mut targets, &expanded)?;
            }
        }
        Ok((targets, false))
    }

    fn target_cover(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        place: &Place,
        active: &mut Vec<Place>,
    ) -> R<bool> {
        self.work
            .places(std::slice::from_ref(place), self.decl.span)?;
        self.charge(active.len().saturating_mul(1 + place.projections.len()))?;
        if active.contains(place) {
            return Ok(false);
        }
        active.push(place.clone());
        let result = self.target_cover_step(aliases, place, active);
        active.pop();
        result
    }
    fn target_cover_step(
        &self,
        aliases: &HashMap<Place, Vec<Place>>,
        place: &Place,
        active: &mut Vec<Place>,
    ) -> R<bool> {
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
                if targets.is_empty() {
                    return Ok(false);
                }
                for target in targets {
                    self.charge(1 + target.projections.len() + place.projections.len())?;
                    let mut target = target.clone();
                    target
                        .projections
                        .extend_from_slice(&place.projections[index + 1..]);
                    if !self.target_cover(aliases, &target, active)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        Ok(!place.has_deref())
    }
}
