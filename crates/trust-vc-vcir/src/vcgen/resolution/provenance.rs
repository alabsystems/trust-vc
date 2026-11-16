// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Carrier storage transports possible borrowed footprints, not symbolic tokens.
use super::*;
use std::collections::HashMap;

type Origins = Vec<(Place, Vec<Place>)>;

#[derive(Clone, Copy)]
struct Relation<'a> {
    owners: &'a HashMap<Place, Vec<Place>>,
    aliases: &'a HashMap<Place, Vec<Place>>,
    escaped: &'a [Place],
    complete: bool,
}

impl Builder<'_, '_> {
    pub(super) fn borrowed(&self, state: &OwnershipState, place: &Place) -> R<Vec<Place>> {
        self.work
            .places(std::slice::from_ref(place), self.decl.span)?;
        let mut footprints = vec![place.clone()];
        let (targets, _) =
            self.possible_targets(&state.aliases, &state.loans, &state.escaped, place)?;
        self.union(&mut footprints, &targets)?;
        for (index, projection) in place.projections.iter().enumerate() {
            self.charge(1 + index)?;
            if *projection == Projection::Deref {
                let prefix = Place {
                    local: place.local,
                    projections: place.projections[..index].to_vec(),
                };
                if let Some(inherited) = state.loans.get(&prefix) {
                    for source in inherited {
                        self.charge(1 + source.projections.len() + place.projections.len())?;
                        let mut projected = source.clone();
                        projected
                            .projections
                            .extend_from_slice(&place.projections[index + 1..]);
                        self.union(&mut footprints, std::slice::from_ref(&projected))?;
                    }
                }
            }
        }
        Ok(footprints)
    }

    pub(super) fn value_provenance(
        &self,
        state: &OwnershipState,
        value: &Expr,
        dest: &Place,
        refs: &[Place],
    ) -> R<Origins> {
        super::super::aux_work::expression(self.work.remaining(), value, value.span)?;
        self.provenance(
            Relation {
                owners: &state.loans,
                aliases: &state.aliases,
                escaped: &state.escaped,
                complete: false,
            },
            value,
            dest,
            refs,
            0,
        )
    }

    pub(super) fn value_aliases(
        &self,
        state: &OwnershipState,
        value: &Expr,
        dest: &Place,
        refs: &[Place],
    ) -> R<Origins> {
        super::super::aux_work::expression(self.work.remaining(), value, value.span)?;
        self.provenance(
            Relation {
                owners: &state.aliases,
                aliases: &state.aliases,
                escaped: &[],
                complete: true,
            },
            value,
            dest,
            refs,
            0,
        )
    }

    pub(super) fn borrow_contents(
        &self,
        state: &OwnershipState,
        source: &Place,
        dest: LocalId,
    ) -> R<(Origins, Origins)> {
        self.charge(2)?;
        let inner = Place {
            local: dest,
            projections: vec![Projection::Deref],
        };
        let loans = self.remap(
            Relation {
                owners: &state.loans,
                aliases: &state.aliases,
                escaped: &state.escaped,
                complete: false,
            },
            source,
            &inner,
        )?;
        let aliases = self.remap(
            Relation {
                owners: &state.aliases,
                aliases: &state.aliases,
                escaped: &[],
                complete: true,
            },
            source,
            &inner,
        )?;
        Ok((loans, aliases))
    }

    fn provenance(
        &self,
        state: Relation<'_>,
        value: &Expr,
        dest: &Place,
        refs: &[Place],
        depth: usize,
    ) -> R<Origins> {
        self.charge(1 + dest.projections.len())?;
        if depth > 64 {
            return Err(refusal(
                "resolution-type",
                "carrier provenance depth exhausted",
                value.span,
            ));
        }
        match &value.kind {
            ExprKind::Read(source) => {
                if self.kept_place(source)? {
                    self.remap(state, source, dest)
                } else {
                    Ok(Vec::new())
                }
            }
            ExprKind::Tuple(fields) | ExprKind::Ctor { fields, .. } => {
                let mut origins = Vec::new();
                for (index, field) in fields.iter().enumerate() {
                    if let ExprKind::Ctor { adt, variant, .. } = &value.kind {
                        let metadata = self
                            .ctx
                            .adts
                            .get(adt)
                            .and_then(|adt| adt.variants.get(*variant as usize))
                            .and_then(|variant| variant.fields.get(index))
                            .ok_or_else(|| {
                                refusal(
                                    "resolution-type",
                                    "missing constructor field mode",
                                    value.span,
                                )
                            })?;
                        if metadata.mode == Mode::Spec {
                            continue;
                        }
                    }
                    self.work
                        .places(std::slice::from_ref(dest), self.decl.span)?;
                    let mut child = dest.clone();
                    child.projections.push(match &value.kind {
                        ExprKind::Ctor { variant, .. } => Projection::Field {
                            variant: *variant,
                            field: index as u32,
                        },
                        _ => Projection::TupleField(index as u32),
                    });
                    let rows = self.provenance(state, field, &child, refs, depth + 1)?;
                    self.combine(&mut origins, rows)?;
                }
                Ok(origins)
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => self.projected(
                state,
                base,
                Projection::Field {
                    variant: *variant,
                    field: *field,
                },
                dest,
                refs,
                depth,
            ),
            ExprKind::TupleField { base, index } => self.projected(
                state,
                base,
                Projection::TupleField(*index),
                dest,
                refs,
                depth,
            ),
            ExprKind::If {
                then_expr,
                else_expr,
                ..
            } => {
                let mut origins = self.provenance(state, then_expr, dest, refs, depth + 1)?;
                let no = self.provenance(state, else_expr, dest, refs, depth + 1)?;
                if state.complete {
                    for (owner, _) in &origins {
                        self.charge((1 + owner.projections.len()).saturating_mul(1 + no.len()))?;
                    }
                    origins.retain(|(owner, _)| no.iter().any(|(other, _)| owner == other));
                    for (owner, targets) in no {
                        self.charge(origins.len().saturating_mul(1 + owner.projections.len()))?;
                        if let Some((_, existing)) =
                            origins.iter_mut().find(|(other, _)| *other == owner)
                        {
                            self.union(existing, &targets)?;
                        }
                    }
                } else {
                    self.combine(&mut origins, no)?;
                }
                Ok(origins)
            }
            ExprKind::MutRefUpdate { reference, value } => {
                let mut origins = self.provenance(state, reference, dest, refs, depth + 1)?;
                let mut inner = dest.clone();
                inner.projections.push(Projection::Deref);
                self.charge(origins.len().saturating_mul(1 + inner.projections.len()))?;
                origins.retain(|(owner, _)| {
                    !(owner.local == inner.local
                        && owner.projections.starts_with(&inner.projections))
                });
                let updates = self.provenance(state, value, &inner, refs, depth + 1)?;
                self.combine(&mut origins, updates)?;
                Ok(origins)
            }
            // Other origins are rejected by the ordinary owned-origin gate.
            // Conservatively retain every possible footprint if one reaches
            // this analysis; lack of provenance never releases a loan.
            _ => {
                if state.complete {
                    return Ok(Vec::new());
                }
                let mut footprints = Vec::new();
                for existing in state.owners.values() {
                    self.union(&mut footprints, existing)?;
                }
                self.union(&mut footprints, state.escaped)?;
                let mut origins = Vec::new();
                for owner in refs {
                    self.charge(1 + owner.projections.len())?;
                    if owner.local == dest.local && owner.projections.starts_with(&dest.projections)
                    {
                        self.work
                            .places(std::slice::from_ref(owner), self.decl.span)?;
                        self.work.places(&footprints, self.decl.span)?;
                        origins.push((owner.clone(), footprints.clone()));
                    }
                }
                Ok(origins)
            }
        }
    }

    fn remap(&self, state: Relation<'_>, source: &Place, dest: &Place) -> R<Origins> {
        let mut origins = Vec::new();
        let mut sources = if state.complete {
            Vec::new()
        } else {
            self.possible_targets(state.aliases, state.owners, state.escaped, source)?
                .0
        };
        self.union(&mut sources, std::slice::from_ref(source))?;
        for source in sources {
            for (owner, footprints) in state.owners {
                self.charge(1 + owner.projections.len() + source.projections.len())?;
                if owner.local == source.local && owner.projections.starts_with(&source.projections)
                {
                    self.charge(1 + dest.projections.len() + owner.projections.len())?;
                    let mut mapped = dest.clone();
                    mapped
                        .projections
                        .extend_from_slice(&owner.projections[source.projections.len()..]);
                    self.work.places(footprints, self.decl.span)?;
                    self.combine(&mut origins, vec![(mapped, footprints.clone())])?;
                }
            }
        }
        Ok(origins)
    }

    fn projected(
        &self,
        state: Relation<'_>,
        base: &Expr,
        projection: Projection,
        dest: &Place,
        refs: &[Place],
        depth: usize,
    ) -> R<Origins> {
        if let (Projection::Field { variant, field }, Ty::Adt(id, _)) = (&projection, &base.ty) {
            let metadata = self
                .ctx
                .adts
                .get(id)
                .and_then(|adt| adt.variants.get(*variant as usize))
                .and_then(|variant| variant.fields.get(*field as usize))
                .ok_or_else(|| {
                    refusal("resolution-type", "missing projected field mode", base.span)
                })?;
            if metadata.mode == Mode::Spec {
                return Ok(Vec::new());
            }
        }
        if let ExprKind::Read(source) = &base.kind {
            self.work
                .places(std::slice::from_ref(source), self.decl.span)?;
            let mut source = source.clone();
            source.projections.push(projection);
            if !self.kept_place(&source)? {
                return Ok(Vec::new());
            }
            return self.remap(state, &source, dest);
        }
        // Compute the temporary product's origins at the destination prefix,
        // then select/remap just the projected owned component.
        let rows = self.provenance(state, base, dest, refs, depth + 1)?;
        let mut selected = Vec::new();
        for (mut owner, footprints) in rows {
            self.charge(1 + owner.projections.len())?;
            if owner.projections.get(dest.projections.len()) == Some(&projection) {
                owner.projections.remove(dest.projections.len());
                selected.push((owner, footprints));
            }
        }
        Ok(selected)
    }

    fn combine(&self, target: &mut Origins, source: Origins) -> R<()> {
        for (owner, footprints) in source {
            self.charge((1 + owner.projections.len()).saturating_mul(1 + target.len()))?;
            if let Some((_, existing)) = target.iter_mut().find(|(old, _)| *old == owner) {
                self.union(existing, &footprints)?;
            } else {
                target.push((owner, footprints));
            }
        }
        Ok(())
    }
}
