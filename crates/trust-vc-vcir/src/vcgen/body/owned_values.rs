// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Logical snapshots remain in values while affine traversal skips their fields.
use super::*;
use crate::vcgen::resolution;

mod abstract_origins;

impl Gen<'_> {
    fn owned_places(&self, ty: &Ty, place: Place, out: &mut Vec<Place>, depth: usize) -> R<()> {
        if !self.classifier.contains(ty, self.decl.span)? {
            return Ok(());
        }
        if depth > 64 {
            return Err(refusal(
                "mut-ref-type",
                "owned move layout exceeds depth bound",
                self.decl.span,
            ));
        }
        match ty {
            Ty::MutRef(_) => out.push(place),
            Ty::Tuple(fields) => {
                for (index, ty) in fields.iter().enumerate() {
                    let mut child = place.clone();
                    child.projections.push(Projection::TupleField(index as u32));
                    self.owned_places(ty, child, out, depth + 1)?;
                }
            }
            Ty::Adt(id, args) => {
                let declaration = self.ctx.adts.get(id).ok_or_else(|| {
                    refusal("mut-ref-type", "unknown owned value type", self.decl.span)
                })?;
                if declaration.kind == crate::AdtKind::Struct && declaration.variants.len() == 1 {
                    for (index, field) in declaration.variants[0].fields.iter().enumerate() {
                        if field.mode == Mode::Spec {
                            continue;
                        }
                        let mut child = place.clone();
                        child.projections.push(Projection::Field {
                            variant: 0,
                            field: index as u32,
                        });
                        self.owned_places(&field.ty.subst(args), child, out, depth + 1)?;
                    }
                } else {
                    out.push(place);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn owned_origin(&self, expression: &Expr) -> R<()> {
        if !self.classifier.contains(&expression.ty, expression.span)? {
            return Ok(());
        }
        match &expression.kind {
            ExprKind::Read(place) if self.kept_place(place, expression.span)? => Ok(()),
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let Ty::Adt(id, _) = &base.ty else {
                    return Err(refusal(
                        "mut-ref-owned-origin",
                        "a field lacks its datatype",
                        expression.span,
                    ));
                };
                let field = self
                    .ctx
                    .adts
                    .get(id)
                    .and_then(|adt| adt.variants.get(*variant as usize))
                    .and_then(|variant| variant.fields.get(*field as usize));
                if field.is_none_or(|field| field.mode == Mode::Spec) {
                    return Err(refusal(
                        "mut-ref-owned-origin",
                        "an owned reference copied from a snapshot field",
                        expression.span,
                    ));
                }
                self.owned_origin(base)
            }
            ExprKind::TupleField { base, .. } => self.owned_origin(base),
            ExprKind::Tuple(fields) => {
                for field in fields {
                    self.owned_origin(field)?;
                }
                Ok(())
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let declaration = self
                    .ctx
                    .adts
                    .get(adt)
                    .and_then(|adt| adt.variants.get(*variant as usize))
                    .ok_or_else(|| {
                        refusal(
                            "mut-ref-owned-origin",
                            "missing constructor field modes",
                            expression.span,
                        )
                    })?;
                if declaration.fields.len() != fields.len() {
                    return Err(refusal(
                        "mut-ref-owned-origin",
                        "constructor field modes disagree",
                        expression.span,
                    ));
                }
                for (value, field) in fields.iter().zip(&declaration.fields) {
                    if field.mode != Mode::Spec {
                        self.owned_origin(value)?;
                    }
                }
                Ok(())
            }
            ExprKind::If {
                then_expr,
                else_expr,
                ..
            } => {
                self.owned_origin(then_expr)?;
                self.owned_origin(else_expr)
            }
            ExprKind::MutRefUpdate { reference, value } => {
                self.owned_origin(reference)?;
                self.owned_origin(value)
            }
            _ => Err(refusal(
                "mut-ref-owned-origin",
                "an owned reference value copied from pure or snapshot storage",
                expression.span,
            )),
        }
    }

    pub(super) fn consume(&self, path: &mut Path, expression: &Expr) -> R<()> {
        self.abstract_owned_origin(path, expression, 0)?;
        // A scalar result can still move owned storage in a nested let value.
        self.owned_origin(expression)?;
        let mut moves = Vec::new();
        resolution::moves(self.ctx, expression, &mut moves);
        for place in moves {
            if !self.kept_place(&place, expression.span)? {
                continue;
            }
            let Some(ty) = resolution::place_ty(self.ctx, self.decl, &place, self.resolution.remaining().unwrap_or(&self.static_work), expression.span)? else {
                continue;
            };
            let mut owned = Vec::new();
            self.owned_places(&ty, place, &mut owned, 0)?;
            for place in owned {
                self.storage_available(path, &place, expression.span)?;
                if !path.moved.contains(&place) {
                    path.moved.push(place);
                }
            }
        }
        Ok(())
    }
}
