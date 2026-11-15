//! Local struct construction and functional updates with source-order values.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::{self as hir, QPath};
use rustc_middle::ty;
use rustc_span::Span;
use trust_vc_vcir::{Expr, ExprKind, LocalId, LocalKind, Mode, Stmt, StmtKind, Ty};

use super::{refuse, Ctx, FnReader, R};

type Binding = (LocalId, Expr, Span);

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn struct_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        _qpath: &'tcx QPath<'tcx>,
        fields: &'tcx [hir::ExprField<'tcx>],
        tail: hir::StructTailExpr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let base = match tail {
            hir::StructTailExpr::None => None,
            hir::StructTailExpr::Base(base) => {
                self.local_struct_source(base, "expr")?;
                Some(base)
            }
            _ => {
                return refuse(
                    "expr",
                    "a struct expression with default or erroneous fields",
                    span,
                )
            }
        };
        let ty = self.expr_ty(e)?;
        let Ty::Adt(adt, _) = ty else {
            return refuse(
                "type",
                "a struct expression of a type VcIR does not know",
                span,
            );
        };
        let rustc_ty = self.expr_rty(e);
        let ty::Adt(adt_def, args) = rustc_ty.kind() else {
            return refuse("expr", "a struct expression of a non-ADT type", span);
        };
        if self.cx.imported_nominal(adt_def.did()).is_some() {
            return refuse(
                "opaque-import",
                "an imported carrier has no constructor or update authority",
                span,
            );
        }
        if !adt_def.is_struct() {
            return refuse("adt", "an enum or union value", span);
        }
        self.check_datatype_access(*adt_def, span, "constructor");
        let count = adt_def.non_enum_variant().fields.len();
        let mut operands: Vec<_> = fields.iter().map(|field| field.expr).collect();
        operands.extend(base);
        // The existing operand lowering freezes values before later effects.
        // Include the base in that same source-order sequence.
        let mut values = self.operands(&operands, ctx, out)?;
        let mut bindings = Vec::new();
        if base.is_some() {
            (values, bindings) = self.save_update_values(values, &operands, ctx, out);
        }
        let base_value = if base.is_some() {
            let Some(value) = values.pop() else {
                return refuse("expr", "a struct update without its base value", span);
            };
            Some(value)
        } else {
            None
        };
        let mut slots: Vec<Option<Expr>> = vec![None; count];
        for (field, value) in fields.iter().zip(values) {
            let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                return refuse(
                    "expr",
                    "a struct field without a compiler index",
                    field.span,
                );
            };
            let Some(slot) = slots.get_mut(index.as_usize()) else {
                return refuse("expr", "a field index out of range", field.span);
            };
            if slot.is_some() {
                return refuse("expr", "a repeated struct field", field.span);
            }
            *slot = Some(value);
        }
        if let (Some(base), Some(value)) = (base, base_value) {
            self.fill_update_fields(e, base, value, *adt_def, args, &mut slots)?;
        }
        let Some(fields) = slots.into_iter().collect::<Option<Vec<_>>>() else {
            return refuse("expr", "a struct expression that misses a field", span);
        };
        let mut result = Expr::new(
            ty,
            self.sp(span),
            ExprKind::Ctor {
                adt,
                variant: 0,
                fields,
            },
        );
        for (local, value, span) in bindings.into_iter().rev() {
            result = Expr::new(
                result.ty.clone(),
                self.sp(span),
                ExprKind::Let {
                    local,
                    value: Box::new(value),
                    body: Box::new(result),
                },
            );
        }
        Ok(result)
    }

    /// Retain every written operand and the base, including an all-fields
    /// update whose result uses no base fields. Pure code uses expression
    /// lets so evaluating one value does not become a statement effect.
    fn save_update_values(
        &mut self,
        values: Vec<Expr>,
        sources: &[&hir::Expr<'_>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> (Vec<Expr>, Vec<Binding>) {
        let mut saved = Vec::new();
        let mut bindings = Vec::new();
        for (value, source) in values.into_iter().zip(sources) {
            let id = if ctx == Ctx::Spec {
                let id = self.add_local(
                    self.local_decl(
                        "_update",
                        value.ty.clone(),
                        Mode::Spec,
                        false,
                        LocalKind::Bound,
                        source.span,
                    ),
                    true,
                );
                bindings.push((id, value, source.span));
                id
            } else {
                let id = self.temp(value.ty.clone(), ctx, source.span);
                out.push(Stmt::new(
                    self.sp(source.span),
                    StmtKind::Let {
                        local: id,
                        init: Some(value),
                    },
                ));
                id
            };
            saved.push(self.read_local(id, source.span));
        }
        (saved, bindings)
    }

    /// Normalize the compiler's instantiated field type in this body's
    /// environment. An unresolved projection remains outside this slice.
    pub(super) fn instantiated_field_rty(
        &self,
        field: &ty::FieldDef,
        args: ty::GenericArgsRef<'tcx>,
        span: Span,
    ) -> R<ty::Ty<'tcx>> {
        let env = ty::TypingEnv::post_analysis(self.tcx, self.body_def);
        match self
            .tcx
            .try_normalize_erasing_regions(env, field.ty(self.tcx, args))
        {
            Ok(ty) => Ok(self.at(ty)),
            Err(_) => refuse(
                "type",
                "a struct field type that cannot be normalized",
                span,
            ),
        }
    }

    fn fill_update_fields(
        &mut self,
        e: &hir::Expr<'_>,
        base: &hir::Expr<'_>,
        value: Expr,
        adt: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        slots: &mut [Option<Expr>],
    ) -> R<()> {
        let base_ty = self.expr_rty(base);
        let ty::Adt(base_adt, base_args) = base_ty.kind() else {
            return refuse(
                "expr",
                "a struct update base that is not an owned struct value",
                base.span,
            );
        };
        if *base_adt != adt || !base_adt.is_struct() || !adt.did().is_local() {
            return refuse(
                "expr",
                "a struct update base of another datatype",
                base.span,
            );
        }
        if self.vc_ty(base_ty)?.as_ref() != Some(&value.ty) {
            return refuse(
                "type",
                "a struct update base with another adjusted type",
                base.span,
            );
        }
        let Some(source_types) = self.typeck.fru_field_types().get(e.hir_id).cloned() else {
            return refuse(
                "expr",
                "a struct update without compiler field types",
                e.span,
            );
        };
        if source_types.len() != slots.len() {
            return refuse(
                "expr",
                "a struct update with inconsistent field types",
                e.span,
            );
        }
        for (index, field) in adt.non_enum_variant().fields.iter().enumerate() {
            let target = self.instantiated_field_rty(field, args, e.span)?;
            let Some(ty) = self.vc_ty(target)? else {
                return refuse("type", "an unsupported instantiated struct field", e.span);
            };
            if let Some(written) = &slots[index] {
                if written.ty != ty {
                    return refuse(
                        "type",
                        "a written struct field of another instantiated type",
                        e.span,
                    );
                }
                continue;
            }
            let source = self.instantiated_field_rty(field, base_args, base.span)?;
            if source != target || self.at(source_types[index]) != source {
                return refuse(
                    "type",
                    "a struct update field needing a type conversion",
                    base.span,
                );
            }
            let Ok(field) = u32::try_from(index) else {
                return refuse("expr", "a struct field index outside VcIR", e.span);
            };
            slots[index] = Some(Expr::new(
                ty,
                self.sp(base.span),
                ExprKind::Field {
                    base: Box::new(value.clone()),
                    variant: 0,
                    field,
                },
            ));
        }
        Ok(())
    }
}
