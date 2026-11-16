//! Typed selectors for the ordinary reader's represented local enum scope.
//!
//! Wrong-variant results remain unspecified by the finite-sum backend. No
//! recommends clause or variant test is inserted as an assumption here.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_ast::{LitKind, Mutability};
use rustc_hir::def_id::DefId;
use rustc_hir::{self as hir};
use rustc_middle::ty;
use rustc_span::Symbol;
use trust_vc_vcir::{Expr, ExprKind, Stmt};

use super::{refuse, Ctx, FnReader, R};

fn literal(expression: &hir::Expr<'_>) -> Option<Symbol> {
    let hir::ExprKind::Lit(value) = expression.kind else {
        return None;
    };
    let LitKind::Str(value, _) = value.node else {
        return None;
    };
    Some(value)
}

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn local_variant_test(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        intrinsic: DefId,
        receiver: &'tcx hir::Expr<'tcx>,
        variant: &'tcx hir::Expr<'tcx>,
        context: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = expression.span;
        let Some(scope) = self.cx.local_variant_fields.as_ref() else {
            return refuse(
                "variant-test",
                "the test has no current local representation scope",
                span,
            );
        };
        if scope.test_intrinsic(self.tcx) != Some(intrinsic)
            || (context == Ctx::Exec && !self.mode_rejected)
        {
            return refuse(
                "variant-test",
                "the local variant test lacks its native identity or ghost context",
                span,
            );
        }
        let Some(name) = literal(variant) else {
            return refuse(
                "variant-test",
                "variant metadata must be an actual string literal",
                span,
            );
        };
        let native = self.expr_rty_adj(receiver);
        let native = match native.kind() {
            ty::Ref(_, inner, Mutability::Not) => *inner,
            _ => native,
        };
        let ty::Adt(adt, _) = native.kind() else {
            return refuse("variant-test", "the receiver is not a native enum", span);
        };
        if !scope.permits(self.tcx, adt.did())
            || !adt.is_enum()
            || self.cx.adt_id(adt.did()).is_none()
            || self.cx.imported_nominal(adt.did()).is_some()
            || self.cx.source_opaque_nominal(adt.did())
        {
            return refuse(
                "variant-test",
                "the receiver has no represented local enum declaration",
                span,
            );
        }
        if adt.variants().len() > 1024 {
            return refuse(
                "variant-test",
                "the variant inventory exceeds its bound",
                span,
            );
        }
        let Some(index) = adt
            .variants()
            .iter()
            .position(|variant| variant.ident(self.tcx).name == name)
        else {
            return refuse(
                "variant-test",
                "the metadata names no actual native variant",
                span,
            );
        };
        if !matches!(self.expr_rty(expression).kind(), ty::Bool) {
            return refuse("variant-test", "the actual test result is not bool", span);
        }
        self.check_datatype_access(*adt, span, "variant test");
        let base = self.expr(receiver, context, out)?;
        Ok(Expr::new(
            trust_vc_vcir::Ty::Bool,
            self.sp(span),
            ExprKind::IsVariant {
                base: Box::new(base),
                variant: index as u32,
            },
        ))
    }

    pub(super) fn local_variant_field(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        intrinsic: DefId,
        receiver: &'tcx hir::Expr<'tcx>,
        variant: &'tcx hir::Expr<'tcx>,
        field: &'tcx hir::Expr<'tcx>,
        context: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = expression.span;
        let Some(scope) = self.cx.local_variant_fields.as_ref() else {
            return refuse(
                "variant-field",
                "the field intrinsic has no current local representation scope",
                span,
            );
        };
        if scope.intrinsic(self.tcx) != Some(intrinsic)
            || (context == Ctx::Exec && !self.mode_rejected)
        {
            return refuse(
                "variant-field",
                "the local field intrinsic lacks its native identity or ghost context",
                span,
            );
        }
        let (Some(variant_name), Some(field_name)) = (literal(variant), literal(field)) else {
            return refuse(
                "variant-field",
                "field metadata must be actual string literals",
                span,
            );
        };
        let original_type = self.expr_rty_adj(receiver);
        let receiver_type = match original_type.kind() {
            ty::Ref(_, inner, Mutability::Not) => *inner,
            _ => original_type,
        };
        let ty::Adt(adt, arguments) = receiver_type.kind() else {
            return refuse(
                "variant-field",
                "the selector receiver is not a native enum",
                span,
            );
        };
        // Check scope before reading any field. Imported/foreign/opaque types
        // cannot acquire representation permission from this local token.
        if !scope.permits(self.tcx, adt.did())
            || !adt.is_enum()
            || self.cx.adt_id(adt.did()).is_none()
            || self.cx.imported_nominal(adt.did()).is_some()
            || self.cx.source_opaque_nominal(adt.did())
        {
            return refuse(
                "variant-field",
                "the selector receiver has no represented local enum declaration",
                span,
            );
        }
        if adt.variants().len() > 1024
            || adt
                .variants()
                .iter()
                .try_fold(0usize, |count, variant| {
                    count.checked_add(variant.fields.len())
                })
                .is_none_or(|count| count > 4096)
        {
            return refuse(
                "variant-field",
                "the selector field inventory exceeds its bound",
                span,
            );
        }
        let Some((variant_index, variant)) = adt
            .variants()
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.ident(self.tcx).name == variant_name)
        else {
            return refuse(
                "variant-field",
                "the metadata names no actual native variant",
                span,
            );
        };
        let Some((field_index, field)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, field)| field.ident(self.tcx).name == field_name)
        else {
            return refuse(
                "variant-field",
                "the metadata names no actual native field",
                span,
            );
        };
        let env = if self.subst.is_some() {
            ty::TypingEnv::fully_monomorphized()
        } else {
            ty::TypingEnv::non_body_analysis(self.tcx, self.def_id.to_def_id())
        };
        let field_type = self
            .tcx
            .try_normalize_erasing_regions(env, field.ty(self.tcx, *arguments))
            .map_err(|_| {
                super::FnProblem::Refused(super::Refusal::new(
                    "variant-field",
                    "the actual instantiated field type cannot be normalized",
                    span,
                ))
            })?;
        let result_type = self
            .tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new(self.expr_rty(expression)))
            .map_err(|_| {
                super::FnProblem::Refused(super::Refusal::new(
                    "variant-field",
                    "the actual selector result type cannot be normalized",
                    span,
                ))
            })?;
        if field_type != result_type {
            return refuse(
                "variant-field",
                "the selector result differs from its actual instantiated field",
                span,
            );
        }
        self.check_datatype_access(*adt, span, "field expression");
        let base = self.expr(receiver, context, out)?;
        Ok(Expr::new(
            self.expr_ty(expression)?,
            self.sp(span),
            ExprKind::Field {
                base: Box::new(base),
                variant: variant_index as u32,
                field: field_index as u32,
            },
        ))
    }
}
