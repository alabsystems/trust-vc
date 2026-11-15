//! Irrefutable value bindings through typed tuple and local struct projections.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use rustc_ast::{BindingMode, ByRef};
use rustc_hir::{self as hir, PatKind};
use rustc_middle::ty;
use rustc_span::Span;
use trust_vc_vcir::{Expr, ExprKind, LocalId, LocalKind, Mode, Stmt, StmtKind, Ty};

use super::{refuse, Ctx, FnReader, R};

impl<'tcx> FnReader<'_, 'tcx> {
    /// Bind projections of one saved initializer. Compiler-inferred borrows
    /// need place/ownership semantics and must never become value bindings.
    pub(super) fn value_let_bindings(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Option<Expr>,
        ctx: Ctx,
        kind: LocalKind,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        if self
            .typeck
            .pat_adjustments()
            .get(pat.hir_id)
            .is_some_and(|a| !a.is_empty())
        {
            return refuse(
                "let-pattern",
                "a value pattern with reference adjustments",
                pat.span,
            );
        }
        match pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Binding(BindingMode(ByRef::No, mutability), pat_hir, ident, None) => {
                if self
                    .typeck
                    .pat_binding_modes()
                    .get(pat_hir)
                    .is_some_and(|mode| matches!(mode, BindingMode(ByRef::Yes(..), _)))
                {
                    return refuse(
                        "let-pattern",
                        "a reference binding in a value pattern",
                        pat.span,
                    );
                }
                let rustc_ty = self.pat_rty(pat);
                let Some(ty) = self.vc_ty(rustc_ty)? else {
                    return refuse("type", format!("`{ident}` has type `{rustc_ty}`"), pat.span);
                };
                if value.as_ref().is_some_and(|v| v.ty != ty) {
                    return refuse(
                        "let-pattern",
                        "a binding with a different projected type",
                        pat.span,
                    );
                }
                let id = self.add_local(
                    self.local_decl(
                        ident.name.as_str(),
                        ty,
                        ctx.local_mode(),
                        kind != LocalKind::Bound && mutability.is_mut(),
                        kind,
                        pat.span,
                    ),
                    value.is_some(),
                );
                self.local_ids.insert(pat_hir, id);
                out.push(Stmt::new(
                    self.sp(pat.span),
                    StmtKind::Let {
                        local: id,
                        init: value,
                    },
                ));
                Ok(())
            }
            PatKind::Tuple(..) => self.tuple_pattern(pat, value, ctx, kind, out),
            PatKind::Struct(..) => self.struct_pattern(pat, value, ctx, kind, out),
            PatKind::TupleStruct(..) => self.tuple_struct_pattern(pat, value, ctx, kind, out),
            _ => refuse(
                "let-pattern",
                "an unsupported binding inside a value pattern",
                pat.span,
            ),
        }
    }

    fn pattern_positions(
        &self,
        count: usize,
        written: usize,
        rest: hir::DotDotPos,
        span: Span,
    ) -> R<Vec<usize>> {
        let Some(gap) = count.checked_sub(written) else {
            return refuse("let-pattern", "a value pattern with too many fields", span);
        };
        if rest.as_opt_usize().is_none() && gap != 0 {
            return refuse("let-pattern", "a value pattern with missing fields", span);
        }
        Ok((0..written)
            .map(|position| {
                position
                    + if rest.as_opt_usize().is_some_and(|r| position >= r) {
                        gap
                    } else {
                        0
                    }
            })
            .collect())
    }

    fn tuple_pattern(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Option<Expr>,
        ctx: Ctx,
        kind: LocalKind,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let PatKind::Tuple(parts, rest) = pat.kind else {
            return refuse(
                "let-pattern",
                "an inconsistent compiler pattern shape",
                pat.span,
            );
        };
        let rustc_ty = self.pat_rty(pat);
        let ty::Tuple(fields) = rustc_ty.kind() else {
            return refuse(
                "let-pattern",
                "a tuple pattern on a non-tuple value",
                pat.span,
            );
        };
        let positions = self.pattern_positions(fields.len(), parts.len(), rest, pat.span)?;
        for (part, index) in parts.iter().zip(positions) {
            let projected = if let Some(base) = &value {
                let Some(ty) = self.vc_ty(fields[index])? else {
                    return refuse("type", "an unsupported tuple field type", part.span);
                };
                let Ok(index) = u32::try_from(index) else {
                    return refuse("let-pattern", "a tuple field index outside VcIR", part.span);
                };
                Some(Expr::new(
                    ty,
                    self.sp(part.span),
                    ExprKind::TupleField {
                        base: Box::new(base.clone()),
                        index,
                    },
                ))
            } else {
                None
            };
            self.value_let_bindings(part, projected, ctx, kind, out)?;
        }
        Ok(())
    }

    fn pattern_struct(
        &mut self,
        pat: &hir::Pat<'_>,
        value: &Option<Expr>,
    ) -> R<(ty::AdtDef<'tcx>, ty::GenericArgsRef<'tcx>)> {
        let rustc_ty = self.pat_rty(pat);
        let ty::Adt(adt, args) = rustc_ty.kind() else {
            return refuse(
                "let-pattern",
                "a struct pattern on a non-struct value",
                pat.span,
            );
        };
        if !adt.is_struct() || !adt.did().is_local() {
            return refuse(
                "let-pattern",
                "an enum, union or non-local struct pattern",
                pat.span,
            );
        }
        let Some(ty @ Ty::Adt(..)) = self.vc_ty(rustc_ty)? else {
            return refuse(
                "type",
                "a struct pattern of a type VcIR does not know",
                pat.span,
            );
        };
        if value.as_ref().is_some_and(|v| v.ty != ty) {
            return refuse(
                "let-pattern",
                "a struct pattern with a different initializer type",
                pat.span,
            );
        }
        self.check_datatype_access(*adt, pat.span, "pattern constructor");
        Ok((*adt, *args))
    }

    fn struct_pattern(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Option<Expr>,
        ctx: Ctx,
        kind: LocalKind,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let PatKind::Struct(_, fields, rest) = pat.kind else {
            return refuse(
                "let-pattern",
                "an inconsistent compiler pattern shape",
                pat.span,
            );
        };
        let (adt, args) = self.pattern_struct(pat, &value)?;
        let declared = &adt.non_enum_variant().fields;
        if rest.is_none() && fields.len() != declared.len() {
            return refuse(
                "let-pattern",
                "a struct pattern with missing fields",
                pat.span,
            );
        }
        let mut seen = HashSet::new();
        for field in fields {
            let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                return refuse(
                    "let-pattern",
                    "a struct pattern field without a compiler index",
                    field.span,
                );
            };
            let Some(decl) = declared.get(index) else {
                return refuse(
                    "let-pattern",
                    "a struct pattern field index outside its type",
                    field.span,
                );
            };
            if !seen.insert(index.as_u32()) {
                return refuse("let-pattern", "a repeated struct pattern field", field.span);
            }
            let projected = self.struct_pattern_field(
                field.pat,
                index.as_u32(),
                self.instantiated_field_rty(decl, args, field.span)?,
                &value,
            )?;
            self.value_let_bindings(field.pat, projected, ctx, kind, out)?;
        }
        Ok(())
    }

    fn tuple_struct_pattern(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Option<Expr>,
        ctx: Ctx,
        kind: LocalKind,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let PatKind::TupleStruct(_, parts, rest) = pat.kind else {
            return refuse(
                "let-pattern",
                "an inconsistent compiler pattern shape",
                pat.span,
            );
        };
        let (adt, args) = self.pattern_struct(pat, &value)?;
        let fields = &adt.non_enum_variant().fields;
        let positions = self.pattern_positions(fields.len(), parts.len(), rest, pat.span)?;
        for (part, index) in parts.iter().zip(positions) {
            let Some(field) = fields.iter().nth(index) else {
                return refuse(
                    "let-pattern",
                    "a tuple struct pattern field outside its type",
                    part.span,
                );
            };
            let Ok(index) = u32::try_from(index) else {
                return refuse(
                    "let-pattern",
                    "a tuple struct field index outside VcIR",
                    part.span,
                );
            };
            let projected = self.struct_pattern_field(
                part,
                index,
                self.instantiated_field_rty(field, args, part.span)?,
                &value,
            )?;
            self.value_let_bindings(part, projected, ctx, kind, out)?;
        }
        Ok(())
    }

    fn struct_pattern_field(
        &self,
        part: &'tcx hir::Pat<'tcx>,
        field: u32,
        rustc_ty: ty::Ty<'tcx>,
        value: &Option<Expr>,
    ) -> R<Option<Expr>> {
        let rustc_ty = self.at(rustc_ty);
        if rustc_ty != self.pat_rty(part) {
            return refuse(
                "let-pattern",
                "a struct field pattern with another instantiated type",
                part.span,
            );
        }
        let Some(ty) = self.vc_ty(rustc_ty)? else {
            return refuse(
                "type",
                "an unsupported struct pattern field type",
                part.span,
            );
        };
        let projected = value.as_ref().map(|base| {
            Expr::new(
                ty,
                self.sp(part.span),
                ExprKind::Field {
                    base: Box::new(base.clone()),
                    variant: 0,
                    field,
                },
            )
        });
        Ok(projected)
    }

    pub(super) fn has_struct_pattern(pat: &hir::Pat<'_>) -> bool {
        match pat.kind {
            PatKind::Struct(..) | PatKind::TupleStruct(..) => true,
            PatKind::Tuple(parts, _) => parts.iter().any(Self::has_struct_pattern),
            _ => false,
        }
    }

    fn holds_local_struct(&self, e: &hir::Expr<'_>) -> bool {
        self.expr_rty(e).walk().any(|arg| {
            let Some(ty) = arg.as_type() else {
                return false;
            };
            matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct() && adt.did().is_local())
        })
    }

    /// Follow only value-producing aggregate operands. Ordinary tuple-only
    /// patterns retain their existing treatment; nested struct patterns do
    /// not hide borrowed values in tuple elements or block tails.
    pub(super) fn local_struct_source(&self, e: &hir::Expr<'_>, tag: &'static str) -> R<()> {
        if !self.typeck.expr_adjustments(e).is_empty() {
            return refuse(tag, "a struct value with compiler adjustments", e.span);
        }
        match e.kind {
            hir::ExprKind::DropTemps(inner) | hir::ExprKind::Field(inner, _) => {
                self.local_struct_source(inner, tag)
            }
            hir::ExprKind::Unary(hir::UnOp::Deref, _) => {
                refuse(tag, "a struct value through a borrowed place", e.span)
            }
            hir::ExprKind::Block(block, None) => match block.expr {
                Some(tail) => self.local_struct_source(tail, tag),
                None => Ok(()),
            },
            hir::ExprKind::Tup(elems) => {
                for elem in elems {
                    if self.holds_local_struct(elem) {
                        self.local_struct_source(elem, tag)?;
                    }
                }
                Ok(())
            }
            hir::ExprKind::Call(callee, args) if self.is_struct_ctor(callee) => {
                for arg in args {
                    if self.holds_local_struct(arg) {
                        self.local_struct_source(arg, tag)?;
                    }
                }
                Ok(())
            }
            hir::ExprKind::Struct(_, fields, tail) => {
                for field in fields {
                    if self.holds_local_struct(field.expr) {
                        self.local_struct_source(field.expr, tag)?;
                    }
                }
                if let hir::StructTailExpr::Base(base) = tail {
                    self.local_struct_source(base, tag)?;
                }
                Ok(())
            }
            hir::ExprKind::If(_, then_expr, else_expr) => {
                self.local_struct_source(then_expr, tag)?;
                if let Some(else_expr) = else_expr {
                    self.local_struct_source(else_expr, tag)?;
                }
                Ok(())
            }
            hir::ExprKind::Match(_, arms, _) => {
                for arm in arms {
                    self.local_struct_source(arm.body, tag)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Pure patterns become nested expression lets; even a wildcard retains
    /// evaluation of the initializer and its checks.
    pub(super) fn spec_value_bindings(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Expr,
        span: Span,
    ) -> R<Vec<(LocalId, Expr, Span)>> {
        if let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, ident, None) = pat.kind {
            // Keep the existing plain Spec-let path: a rejected proof block
            // can translate to Unit while its binding retains the compiler
            // type. The recorded source error must reach its proper phase.
            let rustc_ty = self.pat_rty(pat);
            let Some(ty) = self.vc_ty(rustc_ty)? else {
                return refuse("type", format!("`{ident}` has type `{rustc_ty}`"), pat.span);
            };
            let id = self.add_local(
                self.local_decl(
                    ident.name.as_str(),
                    ty,
                    Mode::Spec,
                    false,
                    LocalKind::Bound,
                    pat.span,
                ),
                true,
            );
            self.local_ids.insert(pat_hir, id);
            return Ok(vec![(id, value, span)]);
        }
        let id = self.add_local(
            self.local_decl(
                "_pattern",
                value.ty.clone(),
                Mode::Spec,
                false,
                LocalKind::Bound,
                span,
            ),
            true,
        );
        let mut bindings = vec![(id, value, span)];
        let value = self.read_local(id, span);
        let mut stmts = Vec::new();
        self.value_let_bindings(pat, Some(value), Ctx::Spec, LocalKind::Bound, &mut stmts)?;
        for stmt in stmts {
            let StmtKind::Let {
                local,
                init: Some(value),
            } = stmt.kind
            else {
                return refuse("let-pattern", "a non-binding in a pure value pattern", span);
            };
            bindings.push((local, value, span));
        }
        Ok(bindings)
    }
}
