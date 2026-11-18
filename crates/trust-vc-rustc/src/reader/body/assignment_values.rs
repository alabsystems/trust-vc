//! Preserve the checked result mode of an assignment-valued Unit.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use rustc_hir as hir;
use std::rc::Rc;
use trust_vc_vcir::{Expr, ExprKind, LocalKind, Mode, Stmt, Ty};

use super::{refuse, Ctx, FnProblem, FnReader, Refusal, R};
use crate::reader::modes::AccessKind;

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn assignment_value(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        place: &'tcx hir::Expr<'tcx>,
        context: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if self.mode_rejected {
            // This path only retains diagnostics for a rejected function.
            self.stmt_expr(expression, context, out)?;
            return Ok(self.unit(expression.span));
        }
        let fail = |reason| {
            FnProblem::Refused(Refusal::new(
                "assignment-value-modes",
                reason,
                expression.span,
            ))
        };
        let checked = self.checked_modes.as_ref().ok_or_else(|| {
            fail("an assignment value lacks a complete native mode walk".to_string())
        })?;
        if checked.signature.def_id != self.def_id.to_def_id()
            || checked.signature.body_owner != self.body_def
            || checked.signature.mode != self.mode
            || !std::ptr::eq(self.typeck, self.tcx.typeck(self.body_def))
            || !self
                .cx
                .checked_modes
                .borrow()
                .get(&self.def_id)
                .is_some_and(|current| Rc::ptr_eq(current, checked))
            || !self.expr_rty(expression).is_unit()
        {
            return refuse(
                "assignment-value-modes",
                "an assignment value replaced its native signature, type or complete facts",
                expression.span,
            );
        }
        let availability = checked
            .availability
            .checked(self.tcx, self.def_id, self.body_def)
            .map_err(fail)?;
        let operation = availability.operation_for(expression).map_err(fail)?;
        let usage = availability
            .use_for(place, AccessKind::Assign)
            .map_err(fail)?;
        if operation.kind != AccessKind::Assign
            || operation.place != place.hir_id
            || operation.mode != operation.place_mode
            || operation.mode != usage.mode
            || operation.place_mode != usage.place_mode
        {
            return refuse(
                "assignment-value-modes",
                "an assignment value differs from its original checked destination operation",
                expression.span,
            );
        }
        let mode = operation.mode;
        self.stmt_expr(expression, context, out)?;
        let unit = self.unit(expression.span);
        if mode != Mode::Spec {
            return Ok(unit);
        }
        // A40's Assign result has its checked destination's mode even though
        // its value is Unit. Preserve that pure Unit result as a read, after
        // the actual assignment's effects. This creates no source binding or
        // operation fact, and changes neither the destination nor its value.
        let local = self.add_local(
            self.local_decl(
                "_assignment_unit",
                Ty::Unit,
                mode,
                false,
                LocalKind::Bound,
                expression.span,
            ),
            true,
        );
        Ok(Expr::new(
            Ty::Unit,
            self.sp(expression.span),
            ExprKind::Let {
                local,
                value: Box::new(unit),
                body: Box::new(self.read_local(local, expression.span)),
            },
        ))
    }
}
