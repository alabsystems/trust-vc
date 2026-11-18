//! Genuine native struct layouts and stable field places. No borrow result.
use super::*;
use crate::reader::modes::PlaceUse;

fn join(a: Mode, b: Mode) -> Mode {
    match (a, b) {
        (Mode::Spec, _) | (_, Mode::Spec) => Mode::Spec,
        (Mode::Proof, _) | (_, Mode::Proof) => Mode::Proof,
        _ => Mode::Exec,
    }
}

impl<'tcx> Walk<'_, '_, 'tcx> {
    // Compare with actual native types under the ORIGINAL source frame. This
    // neither normalizes an alias by syntax nor invents a target region.
    pub(super) fn corresponding_type(
        &self,
        root: &RootPlan<'tcx>,
        native: ty::Ty<'tcx>,
        target: &out::Type,
        depth: usize,
    ) -> Result<(), String> {
        self.spend(depth)?;
        let tcx = root.source.tcx;
        let matches = match (native.kind(), target) {
            (ty::Bool, out::Type::Bool) => true,
            (ty::Never, out::Type::Never) => true,
            (ty::Int(actual), out::Type::Signed(expected)) => matches!(
                (actual, expected),
                (ty::IntTy::I8, out::Signed::I8)
                    | (ty::IntTy::I16, out::Signed::I16)
                    | (ty::IntTy::I32, out::Signed::I32)
                    | (ty::IntTy::I64, out::Signed::I64)
                    | (ty::IntTy::I128, out::Signed::I128)
                    | (ty::IntTy::Isize, out::Signed::Isize)
            ),
            (ty::Uint(actual), out::Type::Unsigned(expected)) => matches!(
                (actual, expected),
                (ty::UintTy::U8, out::Unsigned::U8)
                    | (ty::UintTy::U16, out::Unsigned::U16)
                    | (ty::UintTy::U32, out::Unsigned::U32)
                    | (ty::UintTy::U64, out::Unsigned::U64)
                    | (ty::UintTy::U128, out::Unsigned::U128)
                    | (ty::UintTy::Usize, out::Unsigned::Usize)
            ),
            (ty::Tuple(fields), out::Type::Unit) => fields.is_empty(),
            (ty::Tuple(fields), out::Type::Tuple(types)) if fields.len() == types.len() => {
                for (field, target) in fields.iter().zip(types) {
                    self.corresponding_type(root, field, target, depth + 1)?;
                }
                true
            }
            (ty::Param(parameter), out::Type::Parameter(target)) => {
                let generics = tcx.generics_of(root.source.definition);
                if parameter.index as usize >= generics.count() {
                    false
                } else {
                    let definition = generics.param_at(parameter.index as usize, tcx).def_id;
                    self.graph
                        .frames
                        .get(&root.source.definition)
                        .and_then(|frame| frame.type_targets.get(&definition))
                        == Some(target)
                }
            }
            (ty::Adt(adt, args), out::Type::Adt(target, types)) if args.len() == types.len() => {
                let local = adt
                    .did()
                    .as_local()
                    .ok_or("a foreign field type has no original local declaration")?;
                let declaration = self
                    .graph
                    .declaration_ids
                    .get(&local)
                    .ok_or("a field type was not closed in the original graph")?;
                if usize::try_from(target.0).ok() != Some(declaration.0) {
                    false
                } else {
                    for (argument, target) in args.iter().zip(types) {
                        self.spend(depth + 1)?;
                        self.corresponding_type(
                            root,
                            argument.as_type().ok_or(
                                "field region/const arguments require their complete native frame",
                            )?,
                            target,
                            depth + 1,
                        )?;
                    }
                    true
                }
            }
            _ => false,
        };
        if matches {
            Ok(())
        } else {
            Err("a native field changed its full ordered nominal/type/binder relationship".into())
        }
    }

    fn copy_type(&self, ty: &out::Type, depth: usize) -> Result<out::Type, String> {
        self.spend(depth)?;
        Ok(match ty {
            out::Type::Tuple(fields) => out::Type::Tuple(
                fields
                    .iter()
                    .map(|ty| self.copy_type(ty, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            out::Type::Adt(id, fields) => out::Type::Adt(
                *id,
                fields
                    .iter()
                    .map(|ty| self.copy_type(ty, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            out::Type::Reference { .. } => {
                return Err(
                    "retained field references still require the complete native region/loan map"
                        .into(),
                )
            }
            _ => ty.clone(),
        })
    }

    fn field_type(
        &self,
        template: &out::Type,
        parameters: &[(DefId, out::GenericId)],
        arguments: &[out::Type],
        depth: usize,
    ) -> Result<out::Type, String> {
        self.spend(depth)?;
        if parameters.len() != arguments.len() {
            return Err("a field substitution changed its declaration binder arity".into());
        }
        Ok(match template {
            out::Type::Parameter(id) => {
                let mut found = None;
                for (position, (_, parameter)) in parameters.iter().enumerate() {
                    self.spend(depth + 1)?;
                    if parameter == id {
                        if found.replace(position).is_some() {
                            return Err(
                                "a field declaration repeats its native binder identity".into()
                            );
                        }
                    }
                }
                self.copy_type(
                    arguments
                        .get(found.ok_or("a declared field contains a foreign native binder")?)
                        .ok_or("missing actual field type argument")?,
                    depth + 1,
                )?
            }
            out::Type::Tuple(fields) => out::Type::Tuple(
                fields
                    .iter()
                    .map(|ty| self.field_type(ty, parameters, arguments, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            out::Type::Adt(id, fields) => out::Type::Adt(
                *id,
                fields
                    .iter()
                    .map(|ty| self.field_type(ty, parameters, arguments, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            _ => self.copy_type(template, depth + 1)?,
        })
    }

    fn struct_layout(&self, native: ty::Ty<'tcx>) -> Result<DeclarationId, String> {
        self.spend(0)?;
        let ty::Adt(adt, _) = native.kind() else {
            return Err("a struct operation lost its native ADT type".into());
        };
        if !adt.is_struct() {
            return Err("a struct operation cannot use an enum or union layout".into());
        }
        let owner = adt
            .did()
            .as_local()
            .ok_or("a foreign struct has no source layout authority")?;
        let id = *self
            .graph
            .declaration_ids
            .get(&owner)
            .ok_or("the actual struct declaration is absent from the source graph")?;
        let plan = &self.graph.declarations[id.0];
        if plan.source != owner
            || plan.is_enum
            || plan.variants.len() != 1
            || plan.variants[0].source != adt.non_enum_variant().def_id
            || plan.variants[0].fields.len() != adt.non_enum_variant().fields.len()
        {
            return Err("the native struct kind or complete field inventory changed".into());
        }
        self.frame(
            self.graph
                .frames
                .get(&owner)
                .ok_or("the native struct has no original generic frame")?,
        )?;
        Ok(id)
    }

    fn checked_prefix(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
    ) -> Result<(), String> {
        self.spend(0)?;
        if !matches!(root.source.tcx.hir_node(source.hir_id), hir::Node::Expr(current) if std::ptr::eq(current, source))
            || !root.source.typeck.expr_adjustments(source).is_empty()
        {
            return Err(
                "a field place prefix lost its original allocation or has an unmapped adjustment"
                    .into(),
            );
        }
        if root.adjustment_ids.contains(&source.hir_id) {
            let row = root.source.checked.availability.adjustment_for(source)?;
            if !row.kinds.is_empty() || row.reborrow.is_some() {
                return Err("a field prefix needs its exact native reborrow map".into());
            }
            self.adjustments.insert(source.hir_id);
        }
        Ok(())
    }

    fn place(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        usage: &PlaceUse,
        depth: usize,
    ) -> Result<(out::Expr, out::Type, Mode), String> {
        self.spend(depth)?;
        self.checked_prefix(root, source)?;
        let native = root.source.typeck.expr_ty(source);
        let (kind, target, mode) = match source.kind {
            hir::ExprKind::Path(ref path) => {
                let Res::Local(binding) = root.source.typeck.qpath_res(path, source.hir_id) else { return Err("a field place has a nonlocal root".into()); };
                if source.hir_id != usage.local_use || binding != usage.binding { return Err("a field place changed its actual availability root".into()); }
                let id = *self.local_types.get(&binding).ok_or("a field root has no actual mapped storage type")?;
                let node = &self.graph.types[id.0];
                let mode = match node.position { Position::Parameter(mode) | Position::Storage(mode) => mode, _ => return Err("a field root has a foreign storage position".into()) };
                if node.original != native || node.owner != root.source.definition || mode != usage.binding_mode { return Err("a field root changed its native storage/type/mode join".into()); }
                (out::ExprKind::Local(*self.locals.get(&binding).ok_or("missing mapped field-root storage")?), self.ty(id, 0)?, mode)
            }
            hir::ExprKind::Field(..) => self.field_parts(root, source, usage, depth + 1)?,
            _ => return Err("a field prefix requires a direct local/tuple/struct place; dereferences and temporary scopes stay unmaterialized".into()),
        };
        let site = self.site(Origin::Place {
            source,
            access: usage.access,
            native,
            target: self.copy_type(&target, depth + 1)?,
            environment: ty::TypingEnv::post_analysis(root.source.tcx, root.source.definition),
        })?;
        Ok((out::Expr { site, kind }, target, mode))
    }

    fn field_parts(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        usage: &PlaceUse,
        depth: usize,
    ) -> Result<(out::ExprKind, out::Type, Mode), String> {
        self.spend(depth)?;
        let hir::ExprKind::Field(base, _) = source.kind else {
            return Err("field source shape changed".into());
        };
        // Place roots are checked by `place`. Value reads were checked by
        // `observed`, including any exact identity adjustment.
        let (base_value, base_type, base_mode) = self.place(root, base, usage, depth + 1)?;
        let field_index = root
            .source
            .typeck
            .opt_field_index(source.hir_id)
            .ok_or("a native field has no actual compiler field slot")?;
        let index = field_index.as_usize();
        let tcx = root.source.tcx;
        let native = root.source.typeck.expr_ty(source);
        match root.source.typeck.expr_ty(base).kind() {
            ty::Tuple(fields) => {
                let out::Type::Tuple(types) = base_type else {
                    return Err("a tuple prefix changed its represented type".into());
                };
                if fields.get(index).copied() != Some(native) || fields.len() != types.len() {
                    return Err("a tuple field changed its native slot/type".into());
                }
                let target = types
                    .into_iter()
                    .nth(index)
                    .ok_or("a tuple field has no target slot")?;
                self.corresponding_type(root, native, &target, depth + 1)?;
                Ok((
                    out::ExprKind::TupleField {
                        base: Box::new(base_value),
                        field: index,
                    },
                    target,
                    base_mode,
                ))
            }
            ty::Adt(adt, arguments) => {
                let declaration = self.struct_layout(root.source.typeck.expr_ty(base))?;
                self.corresponding_type(
                    root,
                    root.source.typeck.expr_ty(base),
                    &base_type,
                    depth + 1,
                )?;
                let out::Type::Adt(id, types) = base_type else {
                    return Err("a struct prefix changed its nominal target type".into());
                };
                let graph = self.graph;
                let plan = &graph.declarations[declaration.0];
                let field = plan.variants[0]
                    .fields
                    .get(index)
                    .ok_or("a struct field is outside the original declaration")?;
                let actual = adt
                    .non_enum_variant()
                    .fields
                    .get(field_index)
                    .ok_or("a struct field lost its actual native declaration")?;
                let instantiated = tcx
                    .type_of(actual.did)
                    .instantiate(tcx, arguments)
                    .skip_normalization();
                if field.source != actual.did || instantiated != native {
                    return Err("a field access changed its actual declaration/ordered substitution/typeck type".into());
                }
                let template = self.ty(field.ty, 0)?;
                let frame = graph
                    .frames
                    .get(&plan.source)
                    .ok_or("a field declaration lost its native binder frame")?;
                let target =
                    self.field_type(&template, &frame.type_parameters, &types, depth + 1)?;
                if field.mode != Mode::Spec {
                    self.corresponding_type(root, native, &target, depth + 1)?;
                }
                Ok((
                    out::ExprKind::StructField {
                        base: Box::new(base_value),
                        adt: id,
                        types,
                        field: index,
                    },
                    target,
                    join(base_mode, field.mode),
                ))
            }
            _ => Err("a field base is outside the actual tuple/struct place grammar".into()),
        }
    }

    pub(super) fn field_expression(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        mode: Mode,
        erase: bool,
        depth: usize,
    ) -> Result<out::ExprKind, String> {
        self.spend(depth)?;
        let usage = root
            .source
            .checked
            .availability
            .use_for(source, AccessKind::Read)?;
        if usage.mode != mode || usage.erasure != VarErasure::Keep {
            return Err("field erasure/shadow observations still require their complete native storage/loan map".into());
        }
        let (kind, target, place_mode) = self.field_parts(root, source, usage, depth)?;
        if place_mode != usage.place_mode {
            return Err("a field's native binding/field mode relationship changed".into());
        }
        self.uses.insert((usage.place, usage.access));
        if erase {
            let site = self.site(Origin::Generated {
                source,
                rule: GeneratedRule::RetainedReadBeforeErasure,
                target,
            })?;
            Ok(self.observe(vec![out::Expr { site, kind }], out::Inhabited::Unit))
        } else {
            Ok(kind)
        }
    }

    pub(super) fn field_assignment(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        place: &'tcx hir::Expr<'tcx>,
        value: &'tcx hir::Expr<'tcx>,
        depth: usize,
    ) -> Result<out::ExprKind, String> {
        self.spend(depth)?;
        let operation = root.source.checked.availability.operation_for(source)?;
        let usage = root
            .source
            .checked
            .availability
            .use_for(place, AccessKind::Assign)?;
        if operation.kind != AccessKind::Assign
            || operation.place != place.hir_id
            || operation.place_mode != usage.place_mode
            || operation.mode != usage.mode
            || usage.erasure != VarErasure::Keep
        {
            return Err(
                "a field assignment lacks its exact kept native operation/place row".into(),
            );
        }
        let (destination, _, mode) = self.place(root, place, usage, depth + 1)?;
        if mode != usage.place_mode {
            return Err("a field assignment changed its current field/storage modes".into());
        }
        let value = self.expr(root, value, Some(operation.place_mode), depth + 1)?;
        self.operations.insert(operation.expression);
        self.uses.insert((usage.place, usage.access));
        Ok(out::ExprKind::AssignPlace {
            destination: Box::new(destination),
            value: Box::new(value),
        })
    }

    pub(super) fn struct_expression(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        path: &hir::QPath<'tcx>,
        fields: &'tcx [hir::ExprField<'tcx>],
        tail: hir::StructTailExpr<'tcx>,
        erase: bool,
        depth: usize,
    ) -> Result<out::ExprKind, String> {
        self.spend(depth)?;
        if !matches!(tail, hir::StructTailExpr::None) {
            return Err("struct updates/default fields require the exact original base evaluation and move map".into());
        }
        let native = root.source.typeck.expr_ty(source);
        let declaration = self.struct_layout(native)?;
        let ty::Adt(adt, arguments) = native.kind() else {
            unreachable!()
        };
        let (variant, actual) = crate::reader::datatypes::constructor_variant(
            *adt,
            root.source.typeck.qpath_res(path, source.hir_id),
        )
        .ok_or("a struct literal has no actual constructor declaration")?;
        let graph = self.graph;
        let layout = &graph.declarations[declaration.0].variants[0];
        if variant != 0 || actual.def_id != layout.source || fields.len() != layout.fields.len() {
            return Err("a struct literal changed its complete native field inventory".into());
        }
        let target = self.ty(
            *root
                .construction_types
                .get(&source.hir_id)
                .ok_or("a struct literal lacks its closed native retained type")?,
            0,
        )?;
        self.corresponding_type(root, native, &target, depth + 1)?;
        let out::Type::Adt(id, types) = self.copy_type(&target, depth + 1)? else {
            return Err("a struct literal lost its actual nominal target".into());
        };
        for _ in &layout.fields {
            self.spend(depth + 1)?;
        }
        let mut seen = vec![false; layout.fields.len()];
        let mut values = Vec::new();
        for (position, field) in fields.iter().enumerate() {
            self.spend(depth + 1)?;
            let field_index = root
                .source
                .typeck
                .opt_field_index(field.hir_id)
                .ok_or("a struct literal field lacks its native index")?;
            let index = field_index.as_usize();
            if index >= seen.len() || std::mem::replace(&mut seen[index], true) {
                return Err("a struct literal repeats or invents a native field slot".into());
            }
            let planned = &layout.fields[index];
            let actual = &actual.fields[field_index];
            let instantiated = root
                .source
                .tcx
                .type_of(actual.did)
                .instantiate(root.source.tcx, arguments)
                .skip_normalization();
            let argument = root
                .source
                .checked
                .availability
                .argument_for(source, position)?;
            if actual.did != planned.source
                || instantiated != root.source.typeck.expr_ty(field.expr)
                || argument.argument != field.expr.hir_id
                || argument.mode != planned.mode
                || argument.erased != (planned.mode == Mode::Spec)
            {
                return Err(
                    "a written struct field changed its original type/mode/argument occurrence"
                        .into(),
                );
            }
            self.arguments.insert((argument.call, argument.position));
            values.push((
                index,
                self.expr(root, field.expr, Some(planned.mode), depth + 1)?,
            ));
        }
        let kind = out::ExprKind::ConstructStruct {
            adt: id,
            types,
            fields: values,
        };
        if erase {
            let site = self.site(Origin::Generated {
                source,
                rule: GeneratedRule::RetainedCallBeforeErasure,
                target,
            })?;
            Ok(self.observe(vec![out::Expr { site, kind }], out::Inhabited::Unit))
        } else {
            Ok(kind)
        }
    }
}
