//! Ordinary matches over checked scalar values and represented local variants.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use rustc_ast::{BindingMode, ByRef, LitKind};
use rustc_hir::{self as hir, def::Res, PatKind};
use rustc_middle::ty;
use rustc_span::Span;
use trust_vc_vcir::{
    BinOp, Block, DeclProphecy, Expr, ExprKind, IntLit, Lit, LocalKind, Mode, Place, Projection,
    Stmt, StmtKind, Ty,
};

use super::{check_lit_int, refuse, Ctx, FnReader, R};

enum Coverage {
    Any,
    Bool(bool),
    Variant(u32, bool),
    Other,
}

struct Pattern {
    condition: Expr,
    bindings: Vec<Stmt>,
    coverage: Coverage,
}

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn ordinary_match_value(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        scrutinee: &'tcx hir::Expr<'tcx>,
        arms: &'tcx [hir::Arm<'tcx>],
        source: hir::MatchSource,
        context: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if source != hir::MatchSource::Normal
            || arms.is_empty()
            || arms.len() > 1024
            || arms.iter().any(|arm| arm.guard.is_some())
            || self.reading_initializer
        {
            return refuse(
                "match",
                "a guarded, empty, desugared or constant-initializer match",
                expression.span,
            );
        }
        let (scrutinee_mode, result_mode) = {
            let facts = self.checked_modes.as_ref().ok_or_else(|| {
                super::FnProblem::Refused(super::Refusal::new(
                    "match-modes",
                    "the match lacks a completed original mode walk",
                    expression.span,
                ))
            })?;
            if !self
                .cx
                .checked_modes
                .borrow()
                .get(&self.def_id)
                .is_some_and(|canonical| std::rc::Rc::ptr_eq(canonical, facts))
            {
                return refuse(
                    "match-modes",
                    "the match mode facts are not this reader's current selection",
                    expression.span,
                );
            }
            let observed = facts
                .matches
                .for_match(
                    self.tcx,
                    self.def_id,
                    self.body_def,
                    self.typeck,
                    expression,
                    scrutinee,
                    arms,
                )
                .map_err(|reason| {
                    super::FnProblem::Refused(super::Refusal::new(
                        "match-modes",
                        reason,
                        expression.span,
                    ))
                })?;
            (observed.scrutinee_mode, observed.result_mode)
        };
        if context == Ctx::Exec && scrutinee_mode != trust_vc_vcir::Mode::Exec {
            return refuse(
                "match-modes",
                "an exec match has a non-exec native control mode",
                expression.span,
            );
        }
        let native = self.expr_rty(scrutinee);
        // Every successful pattern below also checks its exact projected type.
        // References and imported/opaque carriers acquire no representation.
        match native.kind() {
            ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Tuple(_) => {}
            ty::Adt(adt, _)
                if adt.is_enum()
                    && adt.did().is_local()
                    && self.cx.adt_id(adt.did()).is_some()
                    && self.cx.imported_nominal(adt.did()).is_none()
                    && !self.cx.source_opaque_nominal(adt.did())
                    && self
                        .cx
                        .local_variant_fields
                        .as_ref()
                        .is_some_and(|scope| scope.permits(self.tcx, adt.did())) => {}
            _ => {
                return refuse(
                    "match",
                    "the scrutinee is outside the checked scalar, tuple or local enum scope",
                    scrutinee.span,
                )
            }
        }
        // A kept match consumes its actual pattern bindings, not a snapshot
        // of the entire stable scrutinee. Untracked proof observations and
        // pure Spec matches retain their existing logical value semantics.
        // The retained original-MIR proof also owns these exact Proof moves
        // in the older mode language. A logical snapshot would erase their
        // storage and incorrectly turn a native arm result into Spec data.
        // NativeOwnership is issued only after the complete original body
        // and built MIR join; the shim still must borrow-check that root.
        let native_proof = matches!((context, scrutinee_mode), (Ctx::Proof, Mode::Proof))
            && self.cx.native_ownership.borrow().contains_key(&self.def_id);
        let kept = native_proof
            || self.cx.opts.new_mut_ref
                && matches!(
                    (context, scrutinee_mode),
                    (Ctx::Exec, Mode::Exec) | (Ctx::Proof, Mode::Proof)
                );
        // Lower normally first: attributes, adjustments, native field access,
        // types and complete modes must not be bypassed by place recognition.
        let before = out.len();
        let value = self.expr(scrutinee, context, out)?;
        let stable = kept && self.stable_match_source(scrutinee);
        let (saved, read) = if stable {
            let Some(place) = Self::match_read_place(&value) else {
                return refuse(
                    "match-place",
                    "a stable native scrutinee did not lower to its checked place",
                    scrutinee.span,
                );
            };
            if out.len() != before {
                return refuse(
                    "match-place",
                    "a stable native scrutinee produced an evaluation effect",
                    scrutinee.span,
                );
            }
            (
                None,
                Expr::read(place, value.ty.clone(), self.sp(scrutinee.span)),
            )
        } else {
            // Computed scrutinees really own this once-evaluated value. It is
            // not an alias of a source place, even if its value is equal.
            let local = self.add_local(
                self.local_decl(
                    "_match",
                    value.ty.clone(),
                    if kept {
                        scrutinee_mode
                    } else {
                        context.local_mode()
                    },
                    false,
                    if context == Ctx::Spec {
                        LocalKind::Bound
                    } else {
                        LocalKind::Temp
                    },
                    scrutinee.span,
                ),
                true,
            );
            (Some((local, value)), self.read_local(local, scrutinee.span))
        };
        let mut patterns = Vec::new();
        let mut bodies = Vec::new();
        let mut effects = Vec::new();
        let outer_locals = self.local_ids.clone();
        for arm in arms {
            let lowered: R<_> = (|| {
                let pattern = self.match_value_pattern(arm.pat, read.clone(), context, kept, 0)?;
                let mut statements = Vec::new();
                let body = self.expr(arm.body, context, &mut statements)?;
                Ok((pattern, body, statements))
            })();
            self.local_ids = outer_locals.clone();
            let (pattern, body, statements) = lowered?;
            patterns.push(pattern);
            bodies.push(body);
            effects.push(statements);
        }
        // Rust's successful native check is mandatory. This additional finite
        // coverage check ensures that dropping the final test is justified by
        // precisely the pattern conditions this lowering actually represents.
        let covered = patterns.iter().any(|p| matches!(p.coverage, Coverage::Any)) || match native.kind() {
            ty::Bool => [false, true].into_iter().all(|b| patterns.iter().any(|p| matches!(p.coverage, Coverage::Bool(x) if x == b))),
            ty::Adt(adt, _) if adt.is_enum() => adt.variants().iter().enumerate().all(|(index, _)|
                patterns.iter().any(|p| matches!(p.coverage, Coverage::Variant(v, true) if v as usize == index))),
            _ => false,
        };
        if !covered {
            return refuse(
                "match-coverage",
                "the native match needs a pattern coverage form outside this slice",
                expression.span,
            );
        }
        if context == Ctx::Spec && effects.iter().any(|s| !s.is_empty()) {
            return refuse(
                "effect-in-spec",
                "a match arm has an effect in spec code",
                expression.span,
            );
        }
        if !kept && effects.iter().all(|s| s.is_empty()) {
            let (saved_local, value) = saved.expect("logical matches save their scrutinee value");
            self.locals[saved_local.index()].kind = LocalKind::Bound;
            self.locals[saved_local.index()].mode = scrutinee_mode;
            let mut values = Vec::new();
            for (pattern, mut body) in patterns.iter_mut().zip(bodies) {
                for binding in pattern.bindings.drain(..).rev() {
                    let StmtKind::Let {
                        local,
                        init: Some(init),
                    } = binding.kind
                    else {
                        return refuse(
                            "match",
                            "a spec pattern produced a non-binding effect",
                            expression.span,
                        );
                    };
                    self.locals[local.index()].kind = LocalKind::Bound;
                    self.locals[local.index()].mutable = false;
                    body = Expr::new(
                        body.ty.clone(),
                        binding.span,
                        ExprKind::Let {
                            local,
                            value: Box::new(init),
                            body: Box::new(body),
                        },
                    );
                }
                values.push(body);
            }
            let mut result = values.pop().expect("nonempty checked arms");
            for (pattern, body) in patterns.iter().zip(values).rev() {
                result = Expr::new(
                    result.ty.clone(),
                    self.sp(expression.span),
                    ExprKind::If {
                        cond: Box::new(pattern.condition.clone()),
                        then_expr: Box::new(body),
                        else_expr: Box::new(result),
                    },
                );
            }
            return Ok(Expr::new(
                result.ty.clone(),
                self.sp(expression.span),
                ExprKind::Let {
                    local: saved_local,
                    value: Box::new(value),
                    body: Box::new(result),
                },
            ));
        }
        if let Some((local, value)) = saved {
            out.push(Stmt::new(
                self.sp(scrutinee.span),
                StmtKind::Let {
                    local,
                    init: Some(value),
                },
            ));
        }
        let result_type = if self.expr_rty(expression).is_never() {
            Ty::Unit
        } else {
            self.expr_ty(expression)?
        };
        let returns_value = arms.iter().any(|arm| !self.expr_rty(arm.body).is_never());
        let result = if returns_value {
            let local = if kept {
                self.temp_with_mode(result_type.clone(), result_mode, expression.span)
            } else {
                self.temp(result_type.clone(), context, expression.span)
            };
            if self.locals[local.index()].mode == trust_vc_vcir::Mode::Spec {
                self.locals[local.index()].prophecy = DeclProphecy::DelayedInfer;
            }
            out.push(Stmt::new(
                self.sp(expression.span),
                StmtKind::Let { local, init: None },
            ));
            Some(local)
        } else {
            None
        };
        let mut blocks = Vec::new();
        for (((pattern, body), mut statements), arm) in
            patterns.iter_mut().zip(bodies).zip(effects).zip(arms)
        {
            let mut block = std::mem::take(&mut pattern.bindings);
            // Effectful ghost arms use generated ghost storage; the native
            // binding modes and complete source-mode validation are retained.
            if context.ghost() && !kept {
                for statement in &block {
                    if let StmtKind::Let { local, .. } = statement.kind {
                        if self.locals[local.index()].mode == trust_vc_vcir::Mode::Exec {
                            self.locals[local.index()].mode = trust_vc_vcir::Mode::Spec;
                            self.locals[local.index()].mutable = false;
                        }
                    }
                }
            }
            block.append(&mut statements);
            if !self.expr_rty(arm.body).is_never() {
                if let Some(local) = result {
                    if body.ty != self.locals[local.index()].ty {
                        return refuse(
                            "match",
                            "an arm result differs from its native join type",
                            arm.body.span,
                        );
                    }
                    block.push(Stmt::new(
                        self.sp(arm.body.span),
                        StmtKind::Assign {
                            place: Place::local(local),
                            value: body,
                        },
                    ));
                }
            }
            blocks.push(Block::new(block));
        }
        let mut branch = blocks.pop().expect("nonempty checked arms");
        for (pattern, then_block) in patterns.iter().zip(blocks).rev() {
            branch = Block::new(vec![Stmt::new(
                self.sp(expression.span),
                StmtKind::If {
                    cond: pattern.condition.clone(),
                    then_block,
                    else_block: branch,
                },
            )]);
        }
        out.extend(branch.stmts);
        if let Some(local) = result {
            return Ok(self.read_local(local, expression.span));
        }
        if result_type == Ty::Unit {
            return Ok(self.unit(expression.span));
        }
        // Every native arm has type `!`, and every arm has been lowered above
        // under the same checked exhaustiveness and mode facts. Rust may have
        // already coerced the match itself to its enclosing value type. As in
        // diverging_value, this temporary has no reachable read or assignment.
        let local = if kept {
            self.temp_with_mode(result_type, result_mode, expression.span)
        } else {
            self.temp(result_type, context, expression.span)
        };
        out.push(Stmt::new(
            self.sp(expression.span),
            StmtKind::Let { local, init: None },
        ));
        Ok(self.read_local(local, expression.span))
    }

    /// Recognize only native places already supported by ordinary expression
    /// lowering. Every node must be the original, unadjusted node in this
    /// reader's body; calls and computed receivers remain value temporaries.
    fn stable_match_source(&self, mut expression: &'tcx hir::Expr<'tcx>) -> bool {
        loop {
            if expression.hir_id.owner.def_id != self.body_def
                || !self.typeck.expr_adjustments(expression).is_empty()
                || !matches!(self.tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
            {
                return false;
            }
            match expression.kind {
                hir::ExprKind::Path(ref path) => {
                    return matches!(self.typeck.qpath_res(path, expression.hir_id), Res::Local(binding)
                        if binding.owner.def_id == self.body_def && self.local_ids.contains_key(&binding));
                }
                hir::ExprKind::Field(base, _) | hir::ExprKind::DropTemps(base) => {
                    expression = base;
                }
                hir::ExprKind::Unary(hir::UnOp::Deref, base)
                    if matches!(self.expr_rty(base).kind(), ty::Ref(..)) =>
                {
                    expression = base;
                }
                _ => return false,
            }
        }
    }

    /// Recover the same checked place from normal lowering, without invoking
    /// another expression/place walk or treating a computed value as an alias.
    fn match_read_place(mut value: &Expr) -> Option<Place> {
        let mut projections = Vec::new();
        loop {
            match &value.kind {
                ExprKind::Read(place) => {
                    let mut place = place.clone();
                    place.projections.extend(projections.into_iter().rev());
                    return Some(place);
                }
                ExprKind::Field {
                    base,
                    variant,
                    field,
                } => {
                    projections.push(Projection::Field {
                        variant: *variant,
                        field: *field,
                    });
                    value = base;
                }
                ExprKind::TupleField { base, index } => {
                    projections.push(Projection::TupleField(*index));
                    value = base;
                }
                ExprKind::MutRefCurrent(reference) => {
                    projections.push(Projection::Deref);
                    value = reference;
                }
                _ => return None,
            }
        }
    }

    fn match_pattern_projection(
        &self,
        value: &Expr,
        projection: Projection,
        ty: Ty,
        span: Span,
        place_patterns: bool,
    ) -> R<Expr> {
        if place_patterns {
            let ExprKind::Read(place) = &value.kind else {
                return refuse(
                    "match-place",
                    "a kept pattern lost its checked scrutinee place",
                    span,
                );
            };
            let mut place = place.clone();
            place.projections.push(projection);
            // Availability must be checked on the selected field, rather
            // than first reading its entire possibly partially moved root.
            return Ok(Expr::read(place, ty, self.sp(span)));
        }
        let kind = match projection {
            Projection::TupleField(index) => ExprKind::TupleField {
                base: Box::new(value.clone()),
                index,
            },
            Projection::Field { variant, field } => ExprKind::Field {
                base: Box::new(value.clone()),
                variant,
                field,
            },
            Projection::Deref => {
                return refuse("match-pattern", "a reference pattern projection", span);
            }
        };
        Ok(Expr::new(ty, self.sp(span), kind))
    }

    fn match_value_pattern(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Expr,
        context: Ctx,
        place_patterns: bool,
        depth: usize,
    ) -> R<Pattern> {
        if depth > 64
            || !super::attrs::verus_attrs(self.tcx.hir_attrs(pat.hir_id)).is_empty()
            || pat.hir_id.owner.def_id != self.body_def
            || !pat.default_binding_modes
            || !matches!(self.tcx.hir_node(pat.hir_id), hir::Node::Pat(actual) if std::ptr::eq(actual, pat))
            || self
                .typeck
                .pat_adjustments()
                .get(pat.hir_id)
                .is_some_and(|a| !a.is_empty())
        {
            return refuse(
                "match-pattern",
                "a pattern lacks its original unadjusted native identity",
                pat.span,
            );
        }
        let native = self.pat_rty(pat);
        if self.vc_ty(native)?.as_ref() != Some(&value.ty) {
            return refuse(
                "match-pattern",
                "a pattern projection differs from its native type",
                pat.span,
            );
        }
        let truth = Expr::bool_lit(true, self.sp(pat.span));
        match pat.kind {
            PatKind::Wild => Ok(Pattern {
                condition: truth,
                bindings: vec![],
                coverage: Coverage::Any,
            }),
            PatKind::Binding(BindingMode(ByRef::No, _), _, _, None) => {
                let mut bindings = Vec::new();
                self.value_let_bindings(
                    pat,
                    Some(value),
                    context,
                    if context == Ctx::Spec {
                        LocalKind::Bound
                    } else {
                        LocalKind::Let
                    },
                    &mut bindings,
                )?;
                Ok(Pattern {
                    condition: truth,
                    bindings,
                    coverage: Coverage::Any,
                })
            }
            PatKind::Expr(pat_expr) => match pat_expr.kind {
                hir::PatExprKind::Lit { lit, negated } => {
                    let (literal, coverage) = match (lit.node, native.kind()) {
                        (LitKind::Bool(b), ty::Bool) if !negated => {
                            (Expr::bool_lit(b, self.sp(pat.span)), Coverage::Bool(b))
                        }
                        (LitKind::Int(magnitude, _), ty::Int(_) | ty::Uint(_)) => {
                            check_lit_int(
                                pat.span,
                                negated,
                                magnitude.get(),
                                &value.ty,
                                self.cx.architecture,
                            )?;
                            (
                                Expr::new(
                                    value.ty.clone(),
                                    self.sp(pat.span),
                                    ExprKind::Lit(Lit::Int(IntLit {
                                        negative: negated && magnitude.get() != 0,
                                        magnitude: magnitude.get(),
                                    })),
                                ),
                                Coverage::Other,
                            )
                        }
                        _ => {
                            return refuse(
                                "match-pattern",
                                "an unsupported scalar pattern literal",
                                pat.span,
                            )
                        }
                    };
                    Ok(Pattern {
                        condition: Expr::binary(
                            BinOp::Eq,
                            value,
                            literal,
                            Ty::Bool,
                            self.sp(pat.span),
                        ),
                        bindings: vec![],
                        coverage,
                    })
                }
                hir::PatExprKind::Path(ref path) => self.match_variant_pattern(
                    pat,
                    path,
                    pat_expr.hir_id,
                    &[],
                    value,
                    context,
                    place_patterns,
                    depth,
                ),
                _ => refuse(
                    "match-pattern",
                    "an unsupported native pattern expression",
                    pat.span,
                ),
            },
            PatKind::Tuple(parts, rest) => {
                let ty::Tuple(fields) = native.kind() else {
                    return refuse(
                        "match-pattern",
                        "a tuple pattern without its native tuple type",
                        pat.span,
                    );
                };
                let positions =
                    self.pattern_positions(fields.len(), parts.len(), rest, pat.span)?;
                let mut condition = truth;
                let mut bindings = Vec::new();
                let mut any = true;
                for (part, position) in parts.iter().zip(positions) {
                    let Some(field_type) = self.vc_ty(fields[position])? else {
                        return refuse(
                            "match-pattern",
                            "an unrepresented native tuple field",
                            part.span,
                        );
                    };
                    let child_value = self.match_pattern_projection(
                        &value,
                        Projection::TupleField(position as u32),
                        field_type,
                        part.span,
                        place_patterns,
                    )?;
                    let child = self.match_value_pattern(
                        part,
                        child_value,
                        context,
                        place_patterns,
                        depth + 1,
                    )?;
                    any &= matches!(child.coverage, Coverage::Any);
                    condition = Expr::binary(
                        BinOp::And,
                        condition,
                        child.condition,
                        Ty::Bool,
                        self.sp(part.span),
                    );
                    bindings.extend(child.bindings);
                }
                Ok(Pattern {
                    condition,
                    bindings,
                    coverage: if any { Coverage::Any } else { Coverage::Other },
                })
            }
            PatKind::TupleStruct(ref path, parts, rest) => {
                let (_, _, variant, _) = self.checked_match_variant(pat, path, pat.hir_id)?;
                let positions =
                    self.pattern_positions(variant.fields.len(), parts.len(), rest, pat.span)?;
                let fields: Vec<_> = parts.iter().zip(positions).map(|(p, i)| (i, p)).collect();
                self.match_variant_pattern(
                    pat,
                    path,
                    pat.hir_id,
                    &fields,
                    value,
                    context,
                    place_patterns,
                    depth,
                )
            }
            PatKind::Struct(ref path, fields, _) => {
                let mut selected = Vec::new();
                for field in fields {
                    let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                        return refuse(
                            "match-pattern",
                            "a pattern field has no current native index",
                            field.span,
                        );
                    };
                    selected.push((index.as_usize(), field.pat));
                }
                self.match_variant_pattern(
                    pat,
                    path,
                    pat.hir_id,
                    &selected,
                    value,
                    context,
                    place_patterns,
                    depth,
                )
            }
            _ => refuse(
                "match-pattern",
                "a reference, alternative, range or binding-subpattern match",
                pat.span,
            ),
        }
    }

    fn checked_match_variant(
        &self,
        pat: &hir::Pat<'tcx>,
        path: &hir::QPath<'tcx>,
        resolution: hir::HirId,
    ) -> R<(
        ty::AdtDef<'tcx>,
        u32,
        &'tcx ty::VariantDef,
        ty::GenericArgs<'tcx>,
    )> {
        let ty::Adt(adt, arguments) = self.pat_rty(pat).kind() else {
            return refuse(
                "match-pattern",
                "a variant pattern without its native datatype",
                pat.span,
            );
        };
        if !adt.is_enum()
            || !adt.did().is_local()
            || self.cx.adt_id(adt.did()).is_none()
            || self.cx.imported_nominal(adt.did()).is_some()
            || self.cx.source_opaque_nominal(adt.did())
            || !self
                .cx
                .local_variant_fields
                .as_ref()
                .is_some_and(|scope| scope.permits(self.tcx, adt.did()))
        {
            return refuse(
                "match-pattern",
                "the datatype lacks its current local representation scope",
                pat.span,
            );
        }
        let Some((index, variant)) = super::super::datatypes::constructor_variant(
            *adt,
            self.typeck.qpath_res(path, resolution),
        ) else {
            return refuse(
                "match-pattern",
                "the constructor belongs to another native datatype",
                pat.span,
            );
        };
        Ok((*adt, index, variant, *arguments))
    }

    fn match_variant_pattern(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        path: &hir::QPath<'tcx>,
        resolution: hir::HirId,
        fields: &[(usize, &'tcx hir::Pat<'tcx>)],
        value: Expr,
        context: Ctx,
        place_patterns: bool,
        depth: usize,
    ) -> R<Pattern> {
        let (adt, index, variant, arguments) = self.checked_match_variant(pat, path, resolution)?;
        self.check_datatype_access(adt, pat.span, "match");
        let mut condition = Expr::new(
            Ty::Bool,
            self.sp(pat.span),
            ExprKind::IsVariant {
                base: Box::new(value.clone()),
                variant: index,
            },
        );
        let mut bindings = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut irrefutable = true;
        for (position, child) in fields {
            let Some(field) = variant.fields.iter().nth(*position) else {
                return refuse(
                    "match-pattern",
                    "a field lies outside its actual variant",
                    child.span,
                );
            };
            let environment = if self.subst.is_some() {
                ty::TypingEnv::fully_monomorphized()
            } else {
                ty::TypingEnv::non_body_analysis(self.tcx, self.def_id.to_def_id())
            };
            let field_type = self
                .tcx
                .try_normalize_erasing_regions(environment, field.ty(self.tcx, arguments));
            let pattern_type = self.tcx.try_normalize_erasing_regions(
                environment,
                ty::Unnormalized::new(self.pat_rty(child)),
            );
            let (Ok(field_native), Ok(pattern_native)) = (field_type, pattern_type) else {
                return refuse(
                    "match-pattern",
                    "a field type cannot be normalized in its actual reader environment",
                    child.span,
                );
            };
            if !seen.insert(position) || pattern_native != field_native {
                return refuse(
                    "match-pattern",
                    "a duplicate or differently typed native field",
                    child.span,
                );
            }
            let Some(field_type) = self.vc_ty(field_native)? else {
                return refuse(
                    "match-pattern",
                    "an unrepresented native field type",
                    child.span,
                );
            };
            let projected = self.match_pattern_projection(
                &value,
                Projection::Field {
                    variant: index,
                    field: *position as u32,
                },
                field_type,
                child.span,
                place_patterns,
            )?;
            let child =
                self.match_value_pattern(child, projected, context, place_patterns, depth + 1)?;
            irrefutable &= matches!(child.coverage, Coverage::Any);
            condition = Expr::binary(
                BinOp::And,
                condition,
                child.condition,
                Ty::Bool,
                self.sp(pat.span),
            );
            bindings.extend(child.bindings);
        }
        Ok(Pattern {
            condition,
            bindings,
            coverage: Coverage::Variant(index, irrefutable),
        })
    }
}
