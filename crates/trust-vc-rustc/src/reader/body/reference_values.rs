//! Typed value projections from ordinary shared-reference expressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    pub(super) fn shared_reference_value(
        &mut self,
        value: Expr,
        result: Ty,
        context: Ctx,
        span: Span,
    ) -> R<Expr> {
        let Ty::Ref {
            mutable: false,
            inner,
        } = &value.ty
        else {
            return refuse(
                "type",
                "a shared dereference lost its native reference type",
                span,
            );
        };
        if inner.as_ref() != &result {
            return refuse(
                "type",
                "a shared dereference changed its native referent type",
                span,
            );
        }
        if matches!(&value.kind, ExprKind::Read(_) | ExprKind::Borrow(_)) {
            return self.builtin_reference_value(value, result, span);
        }
        // Evaluate the already checked native operand once. A typed local
        // and its ordinary Deref projection preserve the referent type, mode,
        // availability and call checks; no expression is retyped or copied.
        let mode = self.operand_mode(&value, context);
        let mut declaration = self.local_decl(
            "shared_reference_value",
            value.ty.clone(),
            mode,
            false,
            LocalKind::Bound,
            span,
        );
        if mode == Mode::Spec {
            declaration.prophecy = DeclProphecy::DelayedInfer;
        }
        let local = self.add_local(declaration, true);
        let mut place = Place::local(local);
        place.projections.push(Projection::Deref);
        let body = Expr::read(place, result.clone(), self.sp(span));
        Ok(Expr::new(
            result,
            self.sp(span),
            ExprKind::Let {
                local,
                value: Box::new(value),
                body: Box::new(body),
            },
        ))
    }
}
