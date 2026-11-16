// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Finite typed storage and the original backward future-effect analysis.
use super::*;

impl Builder<'_, '_> {
    pub(super) fn candidates(
        &self,
        ty: &Ty,
        place: Place,
        all: &mut Vec<Place>,
        refs: &mut Vec<Place>,
        depth: usize,
    ) -> R<()> {
        self.charge(1 + place.projections.len())?;
        if depth > 64 {
            return Err(refusal(
                "resolution-type",
                "owned-place layout exceeds depth bound",
                self.decl.span,
            ));
        }
        all.push(place.clone());
        match ty {
            Ty::MutRef(inner) => {
                if self.kept_place(&place)? {
                    self.work
                        .places(std::slice::from_ref(&place), self.decl.span)?;
                    refs.push(place.clone());
                }
                let mut child = place;
                child.projections.push(Projection::Deref);
                self.candidates(inner, child, all, refs, depth + 1)?;
            }
            Ty::Tuple(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    self.work
                        .places(std::slice::from_ref(&place), self.decl.span)?;
                    let mut child = place.clone();
                    child.projections.push(Projection::TupleField(index as u32));
                    self.candidates(field, child, all, refs, depth + 1)?;
                }
            }
            Ty::Adt(id, args) => {
                let adt = self.ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "resolution-type",
                        "unknown owned-place datatype",
                        self.decl.span,
                    )
                })?;
                // Variant membership is not an unconditional field witness.
                if adt.kind == AdtKind::Struct && adt.variants.len() == 1 {
                    for (index, field) in adt.variants[0].fields.iter().enumerate() {
                        self.work
                            .places(std::slice::from_ref(&place), self.decl.span)?;
                        let mut child = place.clone();
                        child.projections.push(Projection::Field {
                            variant: 0,
                            field: index as u32,
                        });
                        self.candidates(
                            &self.substituted(&field.ty, args)?,
                            child,
                            all,
                            refs,
                            depth + 1,
                        )?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub(super) fn backward(&self, places: &[Place]) -> R<Vec<Vec<bool>>> {
        let matrix = self.nodes.len().checked_mul(places.len()).ok_or_else(|| {
            refusal(
                "resolution-size",
                "resolution matrix overflow",
                self.decl.span,
            )
        })?;
        self.charge(matrix)?;
        let mut before = vec![vec![true; places.len()]; self.nodes.len()];
        for (column, place) in places.iter().enumerate() {
            before[0][column] = !place.has_deref();
        }
        loop {
            let mut changed = false;
            for index in (1..self.nodes.len()).rev() {
                let node = &self.nodes[index];
                for (column, place) in places.iter().enumerate() {
                    self.charge(
                        (1 + place.projections.len())
                            .saturating_mul(1 + node.events.len() + node.next.len()),
                    )?;
                    let mut value = node.next.iter().all(|next| before[*next][column]);
                    for event in node.events.iter().rev() {
                        match event {
                            Event::Move(target) | Event::Mutate(target)
                                if overlaps(target, place) =>
                            {
                                value = false
                            }
                            Event::Overwrite(target) if covers(target, place) => value = true,
                            Event::Overwrite(target) if overlaps(target, place) => value = false,
                            _ => {}
                        }
                    }
                    if before[index][column] != value {
                        before[index][column] = value;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Ok(before)
    }
    pub(super) fn selected(
        &self,
        places: &[Place],
        row: &[bool],
        state: Option<&OwnershipState>,
    ) -> R<Vec<Place>> {
        let Some(state) = state else {
            return Ok(Vec::new());
        };
        let mut selected = Vec::new();
        for (place, yes) in places.iter().zip(row) {
            self.charge(
                state
                    .initialized
                    .len()
                    .saturating_mul(1 + place.projections.len())
                    .saturating_add(1),
            )?;
            if *yes && state.is_initialized(place) {
                self.charge(1 + place.projections.len())?;
                selected.push(place.clone());
            }
        }
        Ok(selected)
    }
    pub(super) fn resolution_points(&self, places: &[Place], row: &[bool]) -> R<Vec<Place>> {
        // Ordinary facts still require the generator's actual live environment
        // and move mask. Keep a just-dropped carrier visible there, until its
        // final relation has been emitted; the abstract successor has already
        // removed its lexical declaration.
        let mut selected = Vec::new();
        for (place, yes) in places.iter().zip(row) {
            self.charge(1 + place.projections.len())?;
            if *yes {
                selected.push(place.clone());
            }
        }
        Ok(selected)
    }
}
