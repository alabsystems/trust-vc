//! Typed variant provenance for abstract values consumed by kept code.
//!
//! This adds no facts. Copy reads require the current function's checked
//! typing premises and keep all source-place and active-variant guards.
use super::*;

impl Gen<'_> {
    fn abstract_copy_type(&self, ty: &Ty, span: SpanId) -> R<bool> {
        // This helper is reached only for an abstract kept value. Without a
        // declaration premise, an unresolved parameter remains non-Copy.
        if self.decl.copy_premises.is_empty() || self.resolution.remaining().is_none() {
            return Ok(false);
        }
        crate::copy_context::is_copy_with(
            &self.ctx.adts,
            &self.decl.copy_premises,
            ty,
            None,
            |amount| self.resolution.charge(amount, span),
        )
    }
    fn abstract_type_work(&self, ty: &Ty, span: SpanId) -> R<usize> {
        let mut pending = vec![(ty, 0usize)];
        let mut size = 0usize;
        while let Some((ty, depth)) = pending.pop() {
            self.resolution.charge(1, span)?;
            size += 1;
            if depth > 64 {
                return Err(refusal(
                    "abstract-owned-origin",
                    "owned origin type depth exhausted",
                    span,
                ));
            }
            match ty {
                Ty::Tuple(fields) | Ty::Adt(_, fields) | Ty::Projection(_, fields) => {
                    self.resolution.charge(fields.len(), span)?;
                    pending.extend(fields.iter().map(|ty| (ty, depth + 1)));
                }
                Ty::MutRef(inner) | Ty::Ref { inner, .. } => pending.push((inner, depth + 1)),
                _ => {}
            }
        }
        Ok(size)
    }

    fn abstract_substituted(&self, ty: &Ty, args: &[Ty], span: SpanId) -> R<Ty> {
        let mut size = self.abstract_type_work(ty, span)?;
        for argument in args {
            size += self.abstract_type_work(argument, span)?;
        }
        self.resolution.charge(size.saturating_mul(size), span)?;
        if ty.has_projection() || args.iter().any(Ty::has_projection) {
            let work = self.resolution.remaining().ok_or_else(|| refusal(
                "abstract-owned-origin", "projected origin has no original work ledger", span))?;
            self.ctx.substitute_type(ty, args, work, span)
        } else { Ok(ty.subst(args)) }
    }

    fn abstract_projection_type(&self, ty: &Ty, projection: Projection, span: SpanId) -> R<Ty> {
        match (projection, ty) {
            (Projection::Deref, Ty::Ref { inner, .. } | Ty::MutRef(inner)) => {
                self.abstract_type_work(inner, span)?;
                Ok((**inner).clone())
            }
            (Projection::TupleField(index), Ty::Tuple(fields)) => {
                let field = fields.get(index as usize).ok_or_else(|| {
                    refusal("abstract-owned-origin", "missing owned tuple field", span)
                })?;
                self.abstract_type_work(field, span)?;
                Ok(field.clone())
            }
            (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                let declaration = self
                    .ctx
                    .adts
                    .get(id)
                    .filter(|decl| {
                        decl.kind != crate::AdtKind::Opaque && args.len() == decl.type_params.len()
                    })
                    .and_then(|decl| decl.variants.get(variant as usize))
                    .and_then(|variant| variant.fields.get(field as usize))
                    .ok_or_else(|| {
                        refusal(
                            "abstract-owned-origin",
                            "missing instantiated owned field",
                            span,
                        )
                    })?;
                self.abstract_substituted(&declaration.ty, args, span)
            }
            _ => Err(refusal(
                "abstract-owned-origin",
                "owned origin has an unsupported projection",
                span,
            )),
        }
    }

    fn abstract_source_place(
        &self,
        expression: &Expr,
        depth: usize,
        copy_result: bool,
    ) -> R<Option<Place>> {
        self.resolution.charge(1, expression.span)?;
        if depth > 64 {
            return Err(refusal(
                "abstract-owned-origin",
                "owned projection depth exhausted",
                expression.span,
            ));
        }
        let found = match &expression.kind {
            ExprKind::Read(place) => {
                self.price_ownership_place(place, expression.span)?;
                if place.has_deref() && !copy_result {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a referenced pointee is not a fresh owned origin",
                        expression.span,
                    ));
                }
                let root = self.decl.local(place.local).ok_or_else(|| {
                    refusal(
                        "abstract-owned-origin",
                        "missing owned source local",
                        expression.span,
                    )
                })?;
                self.abstract_type_work(&root.ty, expression.span)?;
                let mut ty = root.ty.clone();
                for projection in &place.projections {
                    ty = self.abstract_projection_type(&ty, *projection, expression.span)?;
                }
                if ty != expression.ty {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a source read changed its actual type",
                        expression.span,
                    ));
                }
                Some(place.clone())
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let Some(mut place) = self.abstract_source_place(base, depth + 1, copy_result)?
                else {
                    return Ok(None);
                };
                if self.abstract_projection_type(
                    &base.ty,
                    Projection::Field {
                        variant: *variant,
                        field: *field,
                    },
                    expression.span,
                )? != expression.ty
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a selector changed its actual field type",
                        expression.span,
                    ));
                }
                self.price_ownership_place(&place, expression.span)?;
                place.projections.push(Projection::Field {
                    variant: *variant,
                    field: *field,
                });
                Some(place)
            }
            ExprKind::TupleField { base, index } => {
                let Some(mut place) = self.abstract_source_place(base, depth + 1, copy_result)?
                else {
                    return Ok(None);
                };
                if self.abstract_projection_type(
                    &base.ty,
                    Projection::TupleField(*index),
                    expression.span,
                )? != expression.ty
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a selector changed its actual tuple type",
                        expression.span,
                    ));
                }
                self.price_ownership_place(&place, expression.span)?;
                place.projections.push(Projection::TupleField(*index));
                Some(place)
            }
            _ => None,
        };
        Ok(found)
    }

    fn variant_condition_known(
        &self,
        path: &Path,
        required: &Term,
        negative: bool,
        span: SpanId,
    ) -> R<bool> {
        self.resolution.charge(path.guard.len(), span)?;
        let mut pending: Vec<_> = path.guard.iter().collect();
        while let Some(term) = pending.pop() {
            self.resolution.charge(1, span)?;
            self.price_ownership_term(term, span)?;
            self.price_ownership_term(required, span)?;
            match term {
                Term::And(parts) => {
                    self.resolution.charge(parts.len(), span)?;
                    pending.extend(parts);
                }
                Term::Not(inner) if negative && **inner == *required => return Ok(true),
                _ if !negative && *term == *required => return Ok(true),
                _ => {}
            }
        }
        Ok(false)
    }

    fn owned_enum_variant(
        &self,
        path: &Path,
        ty: &Ty,
        value: &Val,
        variant: u32,
        span: SpanId,
    ) -> R<()> {
        let Ty::Adt(id, args) = ty else {
            return Err(refusal(
                "abstract-owned-origin",
                "a variant origin has no native datatype",
                span,
            ));
        };
        let declaration = self
            .ctx
            .adts
            .get(id)
            .filter(|decl| decl.kind == crate::AdtKind::Enum)
            .ok_or_else(|| {
                refusal(
                    "abstract-owned-origin",
                    "a variant origin has no represented enum",
                    span,
                )
            })?;
        if args.len() != declaration.type_params.len()
            || variant as usize >= declaration.variants.len()
        {
            return Err(refusal(
                "abstract-owned-origin",
                "a variant origin changed its actual type arguments or index",
                span,
            ));
        }
        let test = |index| -> R<Term> {
            if let Some(work) = self.resolution.remaining() {
                super::super::super::inline_work::value(work, value, 1, span)?;
                super::super::super::call_identity::price_layout(self.ctx, ty, work, span)?;
            }
            let Val::Leaf(test) =
                self.ctx
                    .test_enum(ty, &self.types, index, value.clone(), span)?
            else {
                return Err(refusal(
                    "abstract-owned-origin",
                    "a variant test is not a scalar predicate",
                    span,
                ));
            };
            Ok(test)
        };
        if self.variant_condition_known(path, &test(variant)?, false, span)? {
            return Ok(());
        }
        // The prefix is already a typed owned value; its complete enum schema
        // gives exactly one tag. No tester fact is asserted here. Every other
        // tag must be explicitly negated for this SAME SSA value/type args.
        for index in 0..declaration.variants.len() {
            self.resolution.charge(1, span)?;
            if index as u32 != variant
                && !self.variant_condition_known(path, &test(index as u32)?, true, span)?
            {
                return Err(refusal(
                    "abstract-owned-origin",
                    "an owned enum field lacks all current parent variant guards",
                    span,
                ));
            }
        }
        Ok(())
    }

    fn abstract_place_origin(&self, path: &Path, place: &Place, ty: &Ty, span: SpanId) -> R<()> {
        if (place.has_deref() && !self.abstract_copy_type(ty, span)?)
            || !path.declared.contains(&place.local)
            || !self.kept_place(place, span)?
        {
            return Err(refusal(
                "abstract-owned-origin",
                "an abstract owned value comes from logical or borrowed storage",
                span,
            ));
        }
        self.storage_available(path, place, span)?;
        let local = self
            .decl
            .local(place.local)
            .ok_or_else(|| refusal("abstract-owned-origin", "missing source local", span))?;
        let root = path.env.get(&place.local).ok_or_else(|| {
            refusal(
                "abstract-owned-origin",
                "uninitialized abstract source",
                span,
            )
        })?;
        self.abstract_type_work(&local.ty, span)?;
        let mut prefix = Place::local(place.local);
        let mut prefix_ty = local.ty.clone();
        for projection in &place.projections {
            self.price_ownership_place(&prefix, span)?;
            // Copying a value through a reference does not move, release or
            // resolve its pointee. Every prefix still needs current kept
            // storage and the same native field-mode/SSA availability joins.
            if *projection == Projection::Deref {
                self.storage_available(path, &prefix, span)?;
            }
            if !self.kept_place(&prefix, span)? {
                return Err(refusal(
                    "abstract-owned-origin",
                    "a copied source crosses logical storage",
                    span,
                ));
            }
            if let Projection::Field { variant, .. } = projection {
                if let Ty::Adt(id, _) = &prefix_ty {
                    if self
                        .ctx
                        .adts
                        .get(id)
                        .is_some_and(|decl| decl.kind == crate::AdtKind::Enum)
                    {
                        if let Some(work) = self.resolution.remaining() {
                            super::super::super::inline_work::value(
                                work,
                                root,
                                1 + prefix.projections.len(),
                                span,
                            )?;
                            super::super::super::call_identity::price_layout(
                                self.ctx, &local.ty, work, span,
                            )?;
                        }
                        let value = super::super::super::expr::project(
                            self.ctx,
                            &self.types,
                            root,
                            &local.ty,
                            &prefix,
                            span,
                            self.resolution.remaining(),
                        )?;
                        self.owned_enum_variant(path, &prefix_ty, &value, *variant, span)?;
                    }
                }
            }
            prefix_ty = self.abstract_projection_type(&prefix_ty, *projection, span)?;
            prefix.projections.push(*projection);
        }
        self.abstract_type_work(ty, span)?;
        if &prefix_ty != ty {
            return Err(refusal(
                "abstract-owned-origin",
                "an owned projection changed its type",
                span,
            ));
        }
        Ok(())
    }

    pub(super) fn abstract_owned_origin(
        &self,
        path: &Path,
        expression: &Expr,
        depth: usize,
    ) -> R<()> {
        if !path.live
            || is_dead(&path.guard)
            || !self
                .classifier
                .contains_abstract(&expression.ty, expression.span)?
        {
            return Ok(());
        }
        self.resolution.charge(1, expression.span)?;
        if depth > 64 {
            return Err(refusal(
                "abstract-owned-origin",
                "owned value origin depth exhausted",
                expression.span,
            ));
        }
        let copy_result = self.abstract_copy_type(&expression.ty, expression.span)?;
        if let Some(place) = self.abstract_source_place(expression, 0, copy_result)? {
            return self.abstract_place_origin(path, &place, &expression.ty, expression.span);
        }
        match &expression.kind {
            ExprKind::Tuple(fields) => {
                let Ty::Tuple(types) = &expression.ty else {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an owned tuple changed its type",
                        expression.span,
                    ));
                };
                if fields.len() != types.len() {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an owned tuple has incomplete fields",
                        expression.span,
                    ));
                }
                for (field, ty) in fields.iter().zip(types) {
                    self.abstract_type_work(ty, expression.span)?;
                    if &field.ty != ty {
                        return Err(refusal(
                            "abstract-owned-origin",
                            "an owned tuple field changed type",
                            expression.span,
                        ));
                    }
                }
                for field in fields {
                    self.abstract_owned_origin(path, field, depth + 1)?;
                }
                Ok(())
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let Ty::Adt(actual, args) = &expression.ty else {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a constructor origin has no actual datatype",
                        expression.span,
                    ));
                };
                let declaration = self
                    .ctx
                    .adts
                    .get(adt)
                    .filter(|decl| {
                        actual == adt
                            && decl.kind != crate::AdtKind::Opaque
                            && args.len() == decl.type_params.len()
                    })
                    .and_then(|decl| decl.variants.get(*variant as usize))
                    .ok_or_else(|| {
                        refusal(
                            "abstract-owned-origin",
                            "missing actual constructor variant",
                            expression.span,
                        )
                    })?;
                if declaration.fields.len() != fields.len() {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "constructor origin has incomplete fields",
                        expression.span,
                    ));
                }
                for (field, declaration) in fields.iter().zip(&declaration.fields) {
                    self.resolution.charge(1, expression.span)?;
                    if field.ty
                        != self.abstract_substituted(&declaration.ty, args, expression.span)?
                    {
                        return Err(refusal(
                            "abstract-owned-origin",
                            "an owned constructor field changed type",
                            expression.span,
                        ));
                    }
                    if declaration.mode != Mode::Spec {
                        self.abstract_owned_origin(path, field, depth + 1)?;
                    }
                }
                Ok(())
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let ExprKind::Ctor {
                    adt,
                    variant: actual,
                    fields,
                } = &base.kind
                else {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an abstract selector is not a guarded owned place",
                        expression.span,
                    ));
                };
                if !matches!(&base.ty, Ty::Adt(id, _) if id == adt)
                    || self.abstract_projection_type(
                        &base.ty,
                        Projection::Field {
                            variant: *variant,
                            field: *field,
                        },
                        expression.span,
                    )? != expression.ty
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a constructor selector changed its actual datatype or field type",
                        expression.span,
                    ));
                }
                if actual != variant
                    || self
                        .ctx
                        .adts
                        .get(adt)
                        .and_then(|decl| decl.variants.get(*actual as usize))
                        .and_then(|variant| variant.fields.get(*field as usize))
                        .is_none_or(|field| field.mode == Mode::Spec)
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an inactive or logical constructor selector cannot supply ownership",
                        expression.span,
                    ));
                }
                self.abstract_owned_origin(path, base, depth + 1)?;
                let field = fields.get(*field as usize).ok_or_else(|| {
                    refusal(
                        "abstract-owned-origin",
                        "missing owned constructor field",
                        expression.span,
                    )
                })?;
                self.abstract_type_work(&field.ty, expression.span)?;
                if expression.ty != field.ty {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a constructor selector changed its field type",
                        expression.span,
                    ));
                }
                self.abstract_owned_origin(path, field, depth + 1)
            }
            ExprKind::TupleField { base, index } => {
                let ExprKind::Tuple(fields) = &base.kind else {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an abstract tuple selector has no owned source",
                        expression.span,
                    ));
                };
                let Ty::Tuple(types) = &base.ty else {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a tuple selector changed its actual base type",
                        expression.span,
                    ));
                };
                if types.len() != fields.len()
                    || self.abstract_projection_type(
                        &base.ty,
                        Projection::TupleField(*index),
                        expression.span,
                    )? != expression.ty
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a tuple selector changed its actual arity or field type",
                        expression.span,
                    ));
                }
                self.abstract_owned_origin(path, base, depth + 1)?;
                let field = fields.get(*index as usize).ok_or_else(|| {
                    refusal(
                        "abstract-owned-origin",
                        "missing owned tuple field",
                        expression.span,
                    )
                })?;
                self.abstract_type_work(&field.ty, expression.span)?;
                if expression.ty != field.ty {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "a tuple selector changed its field type",
                        expression.span,
                    ));
                }
                self.abstract_owned_origin(path, field, depth + 1)
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                self.abstract_type_work(&expression.ty, expression.span)?;
                if cond.ty != Ty::Bool
                    || then_expr.ty != expression.ty
                    || else_expr.ty != expression.ty
                {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "an owned conditional changed its actual branch types",
                        expression.span,
                    ));
                }
                let reads = self.body_reads(path)?;
                let work = self.resolution.shared_work().ok_or_else(|| {
                    refusal(
                        "resolution-state",
                        "an abstract branch has no original work ledger",
                        expression.span,
                    )
                })?;
                super::super::super::aux_work::expression(&work, cond, expression.span)?;
                let mut translator =
                    Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
                        .with_auxiliary_work(work);
                let condition = translator.bool(cond)?;
                self.called_ok(&translator.called)?;
                if !translator.checks.is_empty() {
                    return Err(refusal(
                        "abstract-owned-origin",
                        "owned branch origin requires a pure checked condition",
                        expression.span,
                    ));
                }
                self.price_ownership_path(path, 2, expression.span)?;
                self.price_ownership_term(&condition, expression.span)?;
                let mut yes = path.clone();
                yes.guard.push(condition.clone());
                let mut no = path.clone();
                no.guard.push(condition.not());
                self.abstract_owned_origin(&yes, then_expr, depth + 1)?;
                self.abstract_owned_origin(&no, else_expr, depth + 1)
            }
            _ => Err(refusal(
                "abstract-owned-origin",
                "a logical or uninterpreted value cannot create abstract ownership",
                expression.span,
            )),
        }
    }
}
