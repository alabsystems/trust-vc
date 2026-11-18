//! Live storage, owned moves and checked resolution for new-mode references.
use super::*;
use crate::vcgen::resolution;

#[derive(Debug, Clone)]
pub(super) struct Loan {
    pub(super) places: Vec<Place>,
    pub(super) reference: Term,
}

impl Gen<'_> {
    pub(super) fn kept_place(&self, place: &Place, span: SpanId) -> R<bool> {
        self.price_ownership_place(place, span)?;
        if let Some(kept) = self.ownership_modes.borrow().get(place).copied() {
            return Ok(kept);
        }
        if let Some(work) = self.resolution.remaining() {
            if let Some(local) = self.decl.local(place.local) {
                super::super::call_identity::price_layout(self.ctx, &local.ty, work, span)?;
            }
            self.price_ownership_place(place, span)?;
        }
        let kept = crate::place_mode::place_mode(self.decl, &self.ctx.adts, place)
            .map(|mode| mode.mode != Mode::Spec && !mode.through_spec_mut_ref)
            .ok_or_else(|| refusal("mut-ref-type", "a place has no checked field modes", span))?;
        if self.resolution.remaining().is_some() {
            self.price_ownership_place(place, span)?;
            self.ownership_modes
                .borrow_mut()
                .insert(place.clone(), kept);
        }
        Ok(kept)
    }
    pub(super) fn storage_available(&self, path: &Path, place: &Place, span: SpanId) -> R<()> {
        if path
            .moved
            .iter()
            .any(|moved| resolution::overlaps(moved, place))
        {
            return Err(refusal(
                "mut-ref-moved",
                "access to moved owned reference storage",
                span,
            ));
        }
        if self
            .active_borrows(path)?
            .iter()
            .any(|borrowed| resolution::overlaps(borrowed, place))
        {
            return Err(refusal(
                "mut-ref-borrowed",
                "access to storage still mutably borrowed",
                span,
            ));
        }
        Ok(())
    }

    pub(super) fn resolve_places(
        &mut self,
        path: &mut Path,
        places: &[Place],
        span: SpanId,
    ) -> R<()> {
        if !path.live || is_dead(&path.guard) {
            return Ok(());
        }
        for place in places {
            if !self.kept_place(place, span)? {
                continue;
            }
            if path
                .moved
                .iter()
                .any(|moved| resolution::overlaps(moved, place))
            {
                continue;
            }
            let Some(root) = path.env.get(&place.local) else {
                continue;
            };
            let Some(local) = self.decl.local(place.local) else {
                continue;
            };
            let abstract_target = self.resolution.value_target(place, span)?;
            let ty = if abstract_target.is_some() {
                self.resolution
                    .value_place_type(self.ctx, self.decl, place, span)?
            } else {
                let Some(ty) = resolution::place_ty(self.ctx, self.decl, place, self.resolution.remaining().unwrap_or(&self.static_work), span)? else {
                    continue;
                };
                ty
            };
            if let Some(target) = abstract_target {
                if target.place() != place || target.ty() != &ty || !matches!(ty, Ty::Param(_) | Ty::Projection(..)) {
                    return Err(refusal(
                        "resolution-type",
                        "abstract resolution target changed type",
                        span,
                    ));
                }
                if let Some(work) = self.resolution.remaining() {
                    // Each projection copies the source value and performs
                    // native-type substitution. Spend the original ledger
                    // before constructing the guard/value terms.
                    let copies =
                        (target.guards().len() + 1).saturating_mul(1 + place.projections.len());
                    super::super::inline_work::value(work, root, copies, span)?;
                    for _ in 0..=target.guards().len() {
                        super::super::call_identity::price_layout(self.ctx, &local.ty, work, span)?;
                    }
                }
                let mut guards = Vec::new();
                for guard in target.guards() {
                    let prefix_ty = self.resolution.value_place_type(
                        self.ctx,
                        self.decl,
                        guard.prefix(),
                        span,
                    )?;
                    if !matches!(&prefix_ty, Ty::Adt(id, _) if *id == guard.datatype()) {
                        return Err(refusal(
                            "resolution-type",
                            "resolution guard changed datatype",
                            span,
                        ));
                    }
                    let prefix = super::super::expr::project(
                        self.ctx,
                        &self.types,
                        root,
                        &local.ty,
                        guard.prefix(),
                        span,
                        self.resolution.remaining(),
                    )?;
                    let Val::Leaf(condition) = self.ctx.test_enum(
                        &prefix_ty,
                        &self.types,
                        guard.variant(),
                        prefix,
                        span,
                    )?
                    else {
                        return Err(refusal(
                            "resolution-type",
                            "a variant guard has no scalar predicate",
                            span,
                        ));
                    };
                    guards.push(condition);
                }
                let value = super::super::expr::project(
                    self.ctx,
                    &self.types,
                    root,
                    &local.ty,
                    place,
                    span,
                    self.resolution.remaining(),
                )?;
                let work = self.resolution.remaining().ok_or_else(||
                    refusal("resolution-state", "an abstract resolution fact lost its caller work", span))?;
                let fact = self.ctx.has_resolved_with_work(&ty, &self.types, value, span, work)?;
                self.resolution.charge(path.guard.len(), span)?;
                for condition in &path.guard {
                    self.price_ownership_term(condition, span)?;
                }
                self.fact(
                    &path.guard,
                    Source::Axiom,
                    Term::implies(Term::and(guards), fact),
                );
                // An abstract HasResolved fact is not a concrete reference
                // identity and must neither release loans nor enter this cache.
                continue;
            }
            if !matches!(ty, Ty::MutRef(_)) {
                continue;
            }
            let value =
                super::super::expr::project(self.ctx, &self.types, root, &local.ty, place, span, Some(&self.static_work))?;
            let Val::Leaf(reference) = &value else {
                return Err(refusal(
                    "resolution-type",
                    "a nonopaque reference value",
                    span,
                ));
            };
            if self.reference_resolved(path, reference)? {
                continue;
            }
            let fact = self
                .ctx
                .has_resolved_with_work(&ty, &self.types, value.clone(), span, &self.static_work)?;
            self.fact(&path.guard, Source::Axiom, fact);
            path.resolved.push(reference.clone());
        }
        Ok(())
    }

    fn writeback(
        &self,
        ty: &Ty,
        old: Val,
        projections: &[Projection],
        value: Val,
        span: SpanId,
    ) -> R<Val> {
        let Some((projection, rest)) = projections.split_first() else {
            return Ok(value);
        };
        match (projection, ty) {
            (Projection::Deref, Ty::MutRef(inner)) => {
                let current =
                    self.ctx
                        .mut_ref_projection_with_work(ty, &self.types, old.clone(), false, span, Some(&self.static_work))?;
                let updated = self.writeback(inner, current, rest, value, span)?;
                self.ctx.mut_ref_update_with_work(ty, &self.types, old, updated, span, Some(&self.static_work))
            }
            (Projection::Deref, Ty::Ref { inner, .. }) => {
                self.writeback(inner, old, rest, value, span)
            }
            (Projection::TupleField(index), Ty::Tuple(fields)) => {
                let ty = fields.get(*index as usize).ok_or_else(|| {
                    refusal("mut-ref-type", "tuple writeback field missing", span)
                })?;
                let child = old.child(*index).cloned().ok_or_else(|| {
                    refusal("mut-ref-type", "tuple writeback value missing", span)
                })?;
                let child = self.writeback(ty, child, rest, value, span)?;
                old.with_child(*index, child)
                    .ok_or_else(|| refusal("mut-ref-type", "tuple writeback layout mismatch", span))
            }
            (Projection::Field { variant: 0, field }, Ty::Adt(id, args)) => {
                let adt = self
                    .ctx
                    .adts
                    .get(id)
                    .filter(|adt| adt.kind == crate::AdtKind::Struct)
                    .ok_or_else(|| refusal("enum", "an enum field writeback", span))?;
                let ty = adt.variants[0]
                    .fields
                    .get(*field as usize)
                    .ok_or_else(|| refusal("mut-ref-type", "struct writeback field missing", span))?
                    .ty
                    .subst(args);
                let child = old.child(*field).cloned().ok_or_else(|| {
                    refusal("mut-ref-type", "struct writeback value missing", span)
                })?;
                let child = self.writeback(&ty, child, rest, value, span)?;
                old.with_child(*field, child).ok_or_else(|| {
                    refusal("mut-ref-type", "struct writeback layout mismatch", span)
                })
            }
            _ => Err(refusal(
                "mut-ref-type",
                "a typed writeback projection mismatch",
                span,
            )),
        }
    }

    pub(super) fn assign(
        &mut self,
        path: &mut Path,
        place: &Place,
        value: Val,
        span: SpanId,
    ) -> R<()> {
        if !path.declared.contains(&place.local) {
            return Err(refusal(
                "vcgen-internal",
                "assignment to undeclared local",
                span,
            ));
        }
        let local = self
            .decl
            .local(place.local)
            .ok_or_else(|| refusal("vcgen-internal", "missing assigned local", span))?;
        let ty = resolution::place_ty(self.ctx, self.decl, place, self.resolution.remaining().unwrap_or(&self.static_work), span)?
            .ok_or_else(|| refusal("mut-ref-type", "invalid assigned place type", span))?;
        let shape = self.ctx.shape_with_work(&ty, self.types.owner(), span, &self.static_work)?;
        let value = self.name_value(path, value, &shape, &local.name)?;
        if place.projections.is_empty() {
            path.env.insert(place.local, value);
        } else {
            // A dereference needs the owned reference on its left, even
            // when the final assignment initializes the referenced storage.
            for (index, projection) in place.projections.iter().enumerate() {
                if *projection == Projection::Deref {
                    let prefix = Place {
                        local: place.local,
                        projections: place.projections[..index].to_vec(),
                    };
                    if path
                        .moved
                        .iter()
                        .any(|moved| resolution::overlaps(moved, &prefix))
                    {
                        return Err(refusal(
                            "mut-ref-moved",
                            "write through a moved reference",
                            span,
                        ));
                    }
                }
            }
            if self
                .active_borrows(path)?
                .iter()
                .any(|borrowed| resolution::overlaps(borrowed, place))
            {
                return Err(refusal(
                    "mut-ref-borrowed",
                    "write to storage still mutably borrowed",
                    span,
                ));
            }
            let old = path.env.get(&place.local).cloned().ok_or_else(|| {
                refusal(
                    "generic-uninitialized",
                    "a projection into a declared local with no value",
                    span,
                )
            })?;
            let updated = self.writeback(&local.ty, old, &place.projections, value, span)?;
            let root_shape = self.ctx.shape_with_work(&local.ty, self.types.owner(), span, &self.static_work)?;
            let updated = self.name_value(path, updated, &root_shape, &local.name)?;
            path.env.insert(place.local, updated);
        }
        path.moved.retain(|moved| {
            !(moved.local == place.local
                && moved.projections.starts_with(&place.projections)
                && !moved.projections[place.projections.len()..].contains(&Projection::Deref))
        });
        Ok(())
    }

    pub(super) fn borrow_mut(
        &mut self,
        path: &mut Path,
        dest: LocalId,
        place: &Place,
        span: SpanId,
    ) -> R<()> {
        if !path.declared.contains(&dest) || path.env.contains_key(&dest) {
            return Err(refusal(
                "mut-ref-destination",
                "mutable borrow needs declared uninitialized destination",
                span,
            ));
        }
        self.storage_available(path, place, span)?;
        let source = self
            .decl
            .local(place.local)
            .ok_or_else(|| refusal("mut-ref-type", "unknown borrowed root", span))?;
        let root = path.env.get(&place.local).ok_or_else(|| {
            refusal(
                "mut-ref-uninitialized",
                "borrow of uninitialized storage",
                span,
            )
        })?;
        let before =
            super::super::expr::project(self.ctx, &self.types, root, &source.ty, place, span, Some(&self.static_work))?;
        let ty = resolution::place_ty(self.ctx, self.decl, place, self.resolution.remaining().unwrap_or(&self.static_work), span)?
            .ok_or_else(|| refusal("mut-ref-type", "invalid borrowed projection", span))?;
        let reference_ty = Ty::MutRef(Box::new(ty));
        let shape = self.ctx.shape_with_work(&reference_ty, self.types.owner(), span, &self.static_work)?;
        let reference = self.fresh_at(&shape, "mutable_borrow", &path.guard)?;
        let current = self.ctx.mut_ref_projection_with_work(
            &reference_ty,
            &self.types,
            reference.clone(),
            false,
            span,
            Some(&self.static_work),
        )?;
        let future = self.ctx.mut_ref_projection_with_work(
            &reference_ty,
            &self.types,
            reference.clone(),
            true,
            span,
            Some(&self.static_work),
        )?;
        let initial = current
            .equal(&before)
            .ok_or_else(|| refusal("mut-ref-type", "borrow current shape mismatch", span))?;
        self.fact(&path.guard, Source::Binding, initial);
        self.assign(path, place, future, span)?;
        self.assign(path, &Place::local(dest), reference.clone(), span)?;
        let Val::Leaf(reference) = reference else {
            return Err(refusal(
                "mut-ref-type",
                "borrow produced nonopaque reference",
                span,
            ));
        };
        let mut footprints = vec![place.clone()];
        // A reborrow still borrows the ancestor storage after resolving an
        // intermediate owned reference value.
        for (index, projection) in place.projections.iter().enumerate() {
            if *projection != Projection::Deref {
                continue;
            }
            let prefix = Place {
                local: place.local,
                projections: place.projections[..index].to_vec(),
            };
            let root = path.env.get(&prefix.local).ok_or_else(|| {
                refusal(
                    "mut-ref-uninitialized",
                    "borrowed reference prefix has no value",
                    span,
                )
            })?;
            let root_ty = &self
                .decl
                .local(prefix.local)
                .ok_or_else(|| refusal("mut-ref-type", "borrowed prefix type missing", span))?
                .ty;
            let prefix_value =
                super::super::expr::project(self.ctx, &self.types, root, root_ty, &prefix, span, Some(&self.static_work))?;
            if let Val::Leaf(prefix_reference) = prefix_value {
                let origin = self.reference_origin(&prefix_reference)?;
                for loan in &path.loans {
                    if self.reference_origin(&loan.reference)? != origin {
                        continue;
                    }
                    for source in &loan.places {
                        let mut projected = source.clone();
                        projected
                            .projections
                            .extend_from_slice(&place.projections[index + 1..]);
                        if !footprints.contains(&projected) {
                            footprints.push(projected);
                        }
                    }
                }
            }
        }
        path.loans.push(Loan {
            places: footprints,
            reference,
        });
        Ok(())
    }
}

#[cfg(test)]
mod conditional_tests;
