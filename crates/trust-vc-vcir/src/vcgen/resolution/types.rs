// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Price typed projections and substitutions before copying their payloads.
use super::*;

impl Builder<'_, '_> {
    pub(super) fn kept_place(&self, place: &Place) -> R<bool> {
        self.charge(1 + place.projections.len())?;
        if let Some(kept) = self.place_modes.borrow().get(place).copied() {
            return Ok(kept);
        }
        let remaining = self.work.remaining().get();
        // A mode lookup clones the original root and substitutes every
        // projected field even when a separate type lookup is cached.
        if self.uncached_place(place)?.is_none() {
            return Err(refusal(
                "resolution-type",
                "a place has no checked type",
                self.decl.span,
            ));
        }
        self.charge(remaining - self.work.remaining().get())?;
        self.charge(1 + place.projections.len())?;
        let kept = crate::place_mode::place_mode(self.decl, &self.ctx.adts, place)
            .map(|mode| mode.mode != Mode::Spec && !mode.through_spec_mut_ref)
            .ok_or_else(|| {
                refusal(
                    "resolution-type",
                    "a place has no checked field modes",
                    self.decl.span,
                )
            })?;
        self.charge(1 + place.projections.len())?;
        self.place_modes.borrow_mut().insert(place.clone(), kept);
        Ok(kept)
    }
    pub(super) fn substituted(&self, ty: &Ty, args: &[Ty]) -> R<Ty> {
        let remaining = self.work.remaining().get();
        self.work.ty(ty, self.decl.span, 0)?;
        for argument in args {
            self.work.ty(argument, self.decl.span, 0)?;
        }
        let size = remaining - self.work.remaining().get();
        self.charge(size.saturating_mul(size))?;
        Ok(ty.subst(args))
    }
    pub(super) fn typed_place(&self, place: &Place) -> R<Option<Ty>> {
        self.charge(1 + place.projections.len())?;
        if let Some(cached) = self.place_types.borrow().get(place) {
            if let Some(ty) = cached {
                self.work.ty(ty, self.decl.span, 0)?;
            }
            return Ok(cached.clone());
        }
        let result = self.uncached_place(place)?;
        self.charge(1 + place.projections.len())?;
        if let Some(ty) = &result {
            self.work.ty(ty, self.decl.span, 0)?;
        }
        self.place_types
            .borrow_mut()
            .insert(place.clone(), result.clone());
        Ok(result)
    }
    fn uncached_place(&self, place: &Place) -> R<Option<Ty>> {
        let Some(local) = self.decl.local(place.local) else {
            return Ok(None);
        };
        self.work.ty(&local.ty, self.decl.span, 0)?;
        let mut ty = local.ty.clone();
        for projection in &place.projections {
            self.charge(1)?;
            ty = match (projection, ty) {
                (Projection::Deref, Ty::MutRef(inner) | Ty::Ref { inner, .. }) => *inner,
                (Projection::TupleField(index), Ty::Tuple(fields)) => {
                    let Some(field) = fields.get(*index as usize) else {
                        return Ok(None);
                    };
                    self.work.ty(field, self.decl.span, 0)?;
                    field.clone()
                }
                (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                    let Some(field) = self
                        .ctx
                        .adts
                        .get(&id)
                        .and_then(|adt| adt.variants.get(*variant as usize))
                        .and_then(|variant| variant.fields.get(*field as usize))
                    else {
                        return Ok(None);
                    };
                    self.substituted(&field.ty, &args)?
                }
                _ => return Ok(None),
            };
        }
        Ok(Some(ty))
    }
    pub(super) fn owns(&self, ty: &Ty) -> R<bool> {
        self.classifier.contains(ty, self.decl.span)
    }
}
