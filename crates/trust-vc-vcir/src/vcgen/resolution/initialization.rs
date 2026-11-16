// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Index immutable aggregate topology once; initialization remains dynamic.
use super::*;
use std::collections::HashMap;

impl Builder<'_, '_> {
    pub(super) fn index_initialization(&mut self, universe: &[Place]) -> R<()> {
        self.charge(universe.len())?;
        let mut positions = HashMap::new();
        for (index, place) in universe.iter().enumerate() {
            // Price both the key payload copy and its hashing/equality lookup.
            self.charge(2usize.saturating_mul(1 + place.projections.len()))?;
            if positions.insert(place.clone(), index).is_some() {
                return Err(refusal(
                    "resolution-type",
                    "duplicate initialization place",
                    self.decl.span,
                ));
            }
        }
        self.charge(universe.len())?;
        let mut children = vec![Vec::new(); universe.len()];
        for (index, child) in universe.iter().enumerate() {
            self.charge(1)?;
            let Some((last, prefix)) = child.projections.split_last() else {
                continue;
            };
            if *last == Projection::Deref {
                continue;
            }
            self.charge(2usize.saturating_mul(1 + prefix.len()))?;
            let parent = Place {
                local: child.local,
                projections: prefix.to_vec(),
            };
            let Some(parent) = positions.get(&parent).copied() else {
                continue;
            };
            self.charge(1)?;
            let row = children.get_mut(parent).ok_or_else(|| {
                refusal(
                    "resolution-type",
                    "invalid initialization parent",
                    self.decl.span,
                )
            })?;
            row.push(index);
        }
        self.initialization_children = children;
        Ok(())
    }

    pub(super) fn reconstruct_initialized(
        &self,
        state: &mut OwnershipState,
        universe: &[Place],
    ) -> R<()> {
        if self.initialization_children.len() != universe.len() {
            return Err(refusal(
                "resolution-type",
                "initialization topology belongs to another universe",
                self.decl.span,
            ));
        }
        // Same reverse-universe order and same nonempty/all-children rule as
        // the original scan. A Deref edge never initializes its carrier.
        for (index, parent) in universe.iter().enumerate().rev() {
            self.charge(1)?;
            let children = &self.initialization_children[index];
            if children.is_empty() {
                continue;
            }
            let mut complete = true;
            for index in children {
                self.charge(1)?;
                let child = universe.get(*index).ok_or_else(|| {
                    refusal(
                        "resolution-type",
                        "invalid initialization child",
                        self.decl.span,
                    )
                })?;
                self.charge(
                    (1 + state.initialized.len()).saturating_mul(1 + child.projections.len()),
                )?;
                if !state.is_initialized(child) {
                    complete = false;
                    break;
                }
            }
            if complete {
                self.charge(
                    (1 + state.initialized.len()).saturating_mul(1 + parent.projections.len()),
                )?;
                if !state.is_initialized(parent) {
                    self.work
                        .places(std::slice::from_ref(parent), self.decl.span)?;
                    state.initialized.push(parent.clone());
                }
            }
        }
        Ok(())
    }
}
