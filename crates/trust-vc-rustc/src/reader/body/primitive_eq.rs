//! Explicit referent reads for the finite primitive spec-equality boundary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    /// The existing builtin reference dereference used by Rust adjustments.
    /// A projected read retains normal VcIR place typing, modes, availability
    /// and lifetime checking; it is not a change to an expression's type.
    pub(super) fn builtin_reference_value(&self, value: Expr, referent: Ty, span: Span) -> R<Expr> {
        match value.kind {
            ExprKind::Borrow(inner) => Ok(*inner),
            ExprKind::Read(mut place) => {
                place.projections.push(Projection::Deref);
                Ok(Expr::read(place, referent, self.sp(span)))
            }
            _ => refuse(
                "adjustment",
                "a dereference of a reference that is not a variable",
                span,
            ),
        }
    }

    /// A40 spec equality compares compatible integer referents by value.
    /// Admit only one actual shared Rust reference to a machine integer and
    /// its exact represented reference type, after the normal compatibility
    /// and mutable-reference gates. Other decorations keep their old path.
    pub(super) fn primitive_spec_eq_value(
        &self,
        source_native: ty::Ty<'tcx>,
        native: ty::Ty<'tcx>,
        value: Expr,
        span: Span,
    ) -> R<Expr> {
        let ty::Ref(_, native_inner, mutability) = native.kind() else {
            return Ok(value);
        };
        if mutability.is_mut() || !matches!(native_inner.kind(), ty::Int(_) | ty::Uint(_)) {
            return Ok(value);
        }
        // An overloaded dereference/borrow must not turn a nominal, boxed,
        // mutable or deeper source type into a newly accepted primitive.
        let ty::Ref(_, source_inner, source_mutability) = source_native.kind() else {
            return Ok(value);
        };
        if source_mutability.is_mut() || source_inner != native_inner {
            return Ok(value);
        }
        let Ty::Ref {
            mutable: false,
            inner,
        } = &value.ty
        else {
            return Ok(value);
        };
        let Some(range) = self.cx.int_range(*native_inner) else {
            return refuse("spec-eq-type", "an unnamed native primitive referent", span);
        };
        let expected = Ty::Int(range);
        if inner.as_ref() != &expected {
            return refuse(
                "spec-eq-type",
                "a primitive reference changed its native referent type",
                span,
            );
        }
        match &value.kind {
            ExprKind::Read(_) => {}
            ExprKind::Borrow(inner) if inner.ty == expected => {}
            _ => return Ok(value),
        }
        self.builtin_reference_value(value, expected, span)
    }
}
