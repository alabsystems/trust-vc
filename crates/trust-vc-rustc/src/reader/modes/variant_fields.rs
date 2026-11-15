//! The native mode rule for the genuine enum-field intrinsic.
//!
//! This checks an original local field, never an imported representation.
//! Its Spec result must still pass the caller's ordinary adjustment walk.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_ast::{LitKind, Mutability};
use rustc_span::Symbol;

use super::*;

const MAX_VARIANT_ENTRIES: usize = 16_384;

fn string_literal(expression: &hir::Expr<'_>) -> Option<Symbol> {
    let hir::ExprKind::Lit(literal) = expression.kind else {
        return None;
    };
    let LitKind::Str(value, _) = literal.node else {
        return None;
    };
    Some(value)
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    pub(super) fn variant_test(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        callee: DefId,
        receiver: &'tcx hir::Expr<'tcx>,
        variant: &'tcx hir::Expr<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        if callee.is_local() || self.cx.variant_test_intrinsic() != Some(callee) {
            return self.unknown(
                "the variant test lacks its current genuine builtin selection",
                expression.span,
            );
        }
        let Some(name) = string_literal(variant) else {
            return self.unknown(
                "the variant test requires an actual string literal",
                expression.span,
            );
        };
        let native = self.typeck.expr_ty_adjusted(receiver);
        let native = match native.kind() {
            ty::Ref(_, inner, Mutability::Not) => *inner,
            _ => native,
        };
        let ty::Adt(adt, _) = native.kind() else {
            return self.unknown("the variant test requires a native enum", expression.span);
        };
        if !adt.did().is_local() || !self.cx.permits_variant_fields(adt.did()) || !adt.is_enum() {
            return self.unknown(
                "the variant test lacks this native representation",
                expression.span,
            );
        }
        if adt.variants().len() > MAX_VARIANT_ENTRIES
            || !adt
                .variants()
                .iter()
                .any(|variant| variant.ident(self.tcx).name == name)
            || !matches!(self.typeck.expr_ty(expression).kind(), ty::Bool)
        {
            return self.unknown(
                "the variant test has invalid native variant or result metadata",
                expression.span,
            );
        }
        if self.block == Ghostness::Exec {
            return self.error(expression.span, msg::TEST_VARIANT_IN_EXEC);
        }
        self.expr(receiver, outer, expect)?;
        Ok(Mode::Spec)
    }

    pub(super) fn variant_field(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        callee: DefId,
        receiver: &'tcx hir::Expr<'tcx>,
        variant: &'tcx hir::Expr<'tcx>,
        field: &'tcx hir::Expr<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        if callee.is_local() || self.cx.variant_field_intrinsic() != Some(callee) {
            return self.unknown(
                "the field intrinsic lacks its current genuine builtin selection",
                expression.span,
            );
        }
        let (Some(variant_name), Some(field_name)) =
            (string_literal(variant), string_literal(field))
        else {
            return self.unknown(
                "the field intrinsic requires actual string literals",
                expression.span,
            );
        };
        let receiver_type = self.typeck.expr_ty_adjusted(receiver);
        let receiver_type = match receiver_type.kind() {
            ty::Ref(_, inner, Mutability::Not) => *inner,
            _ => receiver_type,
        };
        let ty::Adt(adt, arguments) = receiver_type.kind() else {
            return self.unknown(
                "the field intrinsic requires an actual native datatype",
                expression.span,
            );
        };
        // Check permission before inspecting any variant or field inventory.
        // The producer's default context deliberately permits no ADT fields.
        if !adt.did().is_local() || !self.cx.permits_variant_fields(adt.did()) {
            return self.unknown(
                "the field intrinsic cannot inspect this datatype's representation",
                expression.span,
            );
        }
        if adt.is_union() {
            return self.unknown(
                "the variant-field intrinsic cannot read a union",
                expression.span,
            );
        }
        let variants = adt.variants();
        if variants.len() > MAX_VARIANT_ENTRIES
            || variants
                .iter()
                .try_fold(variants.len(), |work, variant| {
                    work.checked_add(variant.fields.len())
                })
                .is_none_or(|work| work > MAX_VARIANT_ENTRIES)
        {
            return self.unknown(
                "the variant-field inventory exceeds its native work bound",
                expression.span,
            );
        }
        let Some(variant) = variants
            .iter()
            .find(|variant| variant.ident(self.tcx).name == variant_name)
        else {
            return self.unknown(
                "the field intrinsic has no such native variant",
                expression.span,
            );
        };
        let Some(field) = variant
            .fields
            .iter()
            .find(|field| field.ident(self.tcx).name == field_name)
        else {
            return self.unknown(
                "the field intrinsic has no such native field",
                expression.span,
            );
        };
        let environment = ty::TypingEnv::post_analysis(self.tcx, self.body_owner);
        let field_type = self
            .tcx
            .try_normalize_erasing_regions(environment, field.ty(self.tcx, arguments));
        let result_type = self.tcx.try_normalize_erasing_regions(
            environment,
            ty::Unnormalized::new(self.typeck.expr_ty(expression)),
        );
        let (Ok(field_type), Ok(result_type)) = (field_type, result_type) else {
            return self.unknown(
                "the field intrinsic type cannot be normalized in its actual body environment",
                expression.span,
            );
        };
        if field_type != result_type {
            return self.unknown(
                "the field intrinsic result differs from the actual instantiated field type",
                expression.span,
            );
        }
        if self.block == Ghostness::Exec {
            return self.error(expression.span, msg::GET_VARIANT_IN_EXEC);
        }
        self.expr(receiver, outer, expect)?;
        if self.tcx.dcx().has_errors().is_some() {
            return self.unknown(
                "native diagnostics invalidate the field intrinsic mode walk",
                expression.span,
            );
        }
        // get_variant=true forces Spec independently of the field's mode.
        // expr_adjusted remains outside this call and rejects Spec NeverToAny.
        Ok(Mode::Spec)
    }
}

#[cfg(test)]
mod tests;
