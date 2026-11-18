//! Guarded abstract values, separate from concrete reference loan carriers.
use super::*;
use crate::{AdtId, SpanId};

#[derive(Clone, Debug)]
pub(in crate::vcgen) struct VariantGuard {
    prefix: Place,
    datatype: AdtId,
    variant: u32,
}

impl VariantGuard {
    pub(in crate::vcgen) fn prefix(&self) -> &Place {
        &self.prefix
    }
    pub(in crate::vcgen) fn datatype(&self) -> AdtId {
        self.datatype
    }
    pub(in crate::vcgen) fn variant(&self) -> u32 {
        self.variant
    }
}

#[derive(Clone, Debug)]
pub(in crate::vcgen) struct ValueTarget {
    place: Place,
    ty: Ty,
    guards: Vec<VariantGuard>,
}

impl ValueTarget {
    pub(in crate::vcgen) fn place(&self) -> &Place {
        &self.place
    }
    pub(in crate::vcgen) fn ty(&self) -> &Ty {
        &self.ty
    }
    pub(in crate::vcgen) fn guards(&self) -> &[VariantGuard] {
        &self.guards
    }
    fn price(&self, work: &state::Work, span: SpanId) -> R<()> {
        work.ty(&self.ty, span, 0)?;
        work.places(std::slice::from_ref(&self.place), span)?;
        for guard in &self.guards {
            work.places(std::slice::from_ref(&guard.prefix), span)?;
            work.charge(1, span)?;
        }
        Ok(())
    }
}

impl Plan {
    pub(in crate::vcgen) fn value_place_type(
        &self,
        ctx: &Ctx<'_>,
        decl: &FnDecl,
        place: &Place,
        span: SpanId,
    ) -> R<Ty> {
        let work = self
            .work
            .as_ref()
            .ok_or_else(|| refusal("resolution-state", "abstract type has no work ledger", span))?;
        let local = decl
            .local(place.local)
            .ok_or_else(|| refusal("resolution-type", "missing abstract source local", span))?;
        work.ty(&local.ty, span, 0)?;
        let mut ty = if local.ty.has_projection() {
            ctx.normalize_type(&local.ty, work.remaining(), span)?
        } else { local.ty.clone() };
        for projection in &place.projections {
            work.charge(1, span)?;
            ty = match (projection, ty) {
                (Projection::TupleField(index), Ty::Tuple(fields)) => {
                    let field = fields.get(*index as usize).ok_or_else(|| {
                        refusal("resolution-type", "invalid abstract tuple field", span)
                    })?;
                    work.ty(field, span, 0)?;
                    field.clone()
                }
                (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                    let field = ctx
                        .adts
                        .get(&id)
                        .filter(|decl| {
                            decl.kind != AdtKind::Opaque && decl.type_params.len() == args.len()
                        })
                        .and_then(|decl| decl.variants.get(*variant as usize))
                        .and_then(|variant| variant.fields.get(*field as usize))
                        .ok_or_else(|| {
                            refusal(
                                "resolution-type",
                                "invalid instantiated abstract field",
                                span,
                            )
                        })?;
                    let before = work.remaining().get();
                    work.ty(&field.ty, span, 0)?;
                    for argument in &args {
                        work.ty(argument, span, 0)?;
                    }
                    let size = before - work.remaining().get();
                    // Price both this current-type join and the following
                    // selector translation before either substitution copy.
                    work.charge(size.saturating_mul(size).saturating_mul(2), span)?;
                    ctx.substitute_type(&field.ty, &args, work.remaining(), span)?
                }
                _ => {
                    return Err(refusal(
                        "resolution-type",
                        "abstract target crosses an unsupported projection",
                        span,
                    ))
                }
            };
        }
        Ok(ty)
    }

    pub(in crate::vcgen) fn value_target(
        &self,
        place: &Place,
        span: SpanId,
    ) -> R<Option<ValueTarget>> {
        for target in &self.value_targets {
            self.charge(
                1 + place.projections.len() + target.place.projections.len(),
                span,
            )?;
            if target.place == *place {
                let work = self.work.as_ref().ok_or_else(|| {
                    refusal(
                        "resolution-state",
                        "abstract target has no work ledger",
                        span,
                    )
                })?;
                target.price(work, span)?;
                return Ok(Some(target.clone()));
            }
        }
        Ok(None)
    }
}

impl Builder<'_, '_> {
    pub(super) fn value_places(&self, values: &[ValueTarget]) -> R<Vec<Place>> {
        let mut places = Vec::new();
        for target in values {
            self.work
                .places(std::slice::from_ref(&target.place), self.decl.span)?;
            places.push(target.place.clone());
        }
        Ok(places)
    }

    pub(super) fn abstract_candidates(
        &self,
        ty: &Ty,
        place: Place,
        guards: &[VariantGuard],
        universe: &mut Vec<Place>,
        targets: &mut Vec<ValueTarget>,
        depth: usize,
    ) -> R<()> {
        self.charge(1 + place.projections.len())?;
        if depth > 64 {
            return Err(refusal(
                "resolution-type",
                "abstract value layout exceeds depth bound",
                self.decl.span,
            ));
        }
        if !self.kept_place(&place)? {
            return Ok(());
        }
        self.charge(universe.len().saturating_mul(1 + place.projections.len()))?;
        if !universe.contains(&place) {
            self.work
                .places(std::slice::from_ref(&place), self.decl.span)?;
            universe.push(place.clone());
        }
        // Preserve every immediate kept child in the initialization topology,
        // including nonabstract siblings. A partial set of fields must never
        // reconstruct initialization of the parent aggregate.
        if !self.classifier.contains_abstract(ty, self.decl.span)? {
            return Ok(());
        }
        match ty {
            Ty::Param(_) | Ty::Projection(..) => {
                // No implicit drop fact for a pointee; concrete references
                // retain their independent existing resolution analysis.
                if place.has_deref() {
                    return Ok(());
                }
                self.work.ty(ty, self.decl.span, 0)?;
                self.work
                    .places(std::slice::from_ref(&place), self.decl.span)?;
                for guard in guards {
                    self.work
                        .places(std::slice::from_ref(&guard.prefix), self.decl.span)?;
                    self.charge(1)?;
                }
                targets.push(ValueTarget {
                    place,
                    ty: ty.clone(),
                    guards: guards.to_vec(),
                });
            }
            Ty::Tuple(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    self.work
                        .places(std::slice::from_ref(&place), self.decl.span)?;
                    let mut child = place.clone();
                    child.projections.push(Projection::TupleField(index as u32));
                    self.abstract_candidates(field, child, guards, universe, targets, depth + 1)?;
                }
            }
            Ty::Adt(id, args) => {
                let adt = self.ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "resolution-type",
                        "missing abstract value datatype",
                        self.decl.span,
                    )
                })?;
                if adt.kind == AdtKind::Opaque || args.len() != adt.type_params.len() {
                    return Err(refusal(
                        "resolution-type",
                        "abstract value lacks represented layout",
                        self.decl.span,
                    ));
                }
                for (variant, declaration) in adt.variants.iter().enumerate() {
                    for (field, declaration) in declaration.fields.iter().enumerate() {
                        self.charge(1)?;
                        if declaration.mode == Mode::Spec {
                            continue;
                        }
                        self.work
                            .places(std::slice::from_ref(&place), self.decl.span)?;
                        let mut child = place.clone();
                        child.projections.push(Projection::Field {
                            variant: variant as u32,
                            field: field as u32,
                        });
                        for guard in guards {
                            self.work
                                .places(std::slice::from_ref(&guard.prefix), self.decl.span)?;
                        }
                        let mut nested = guards.to_vec();
                        if adt.kind == AdtKind::Enum {
                            self.work
                                .places(std::slice::from_ref(&place), self.decl.span)?;
                            nested.push(VariantGuard {
                                prefix: place.clone(),
                                datatype: *id,
                                variant: variant as u32,
                            });
                        }
                        let field_ty = self.substituted(&declaration.ty, args)?;
                        self.abstract_candidates(
                            &field_ty,
                            child,
                            &nested,
                            universe,
                            targets,
                            depth + 1,
                        )?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
