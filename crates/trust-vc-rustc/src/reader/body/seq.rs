// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pure sequence length calls retain ordinary imported-function semantics.

use super::*;

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn owned_seq_index(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        definition: DefId,
        arguments: &[&'tcx hir::Expr<'tcx>],
        context: Ctx,
        output: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if !self.cx.imported_seq_index(definition) || arguments.len() != 2 {
            return refuse("owned-seq-index", "sequence index requires its exact current source-family signature and checked recommendations", expression.span);
        }
        let argument_owner = match expression.kind {
            hir::ExprKind::Call(function, _) => function.hir_id,
            hir::ExprKind::MethodCall(..) => expression.hir_id,
            _ => {
                return refuse(
                    "owned-seq-index",
                    "sequence index is not an actual native function or method call",
                    expression.span,
                )
            }
        };
        self.call_fn(
            expression,
            definition,
            self.typeck.node_args(argument_owner),
            arguments,
            context,
            output,
            false,
        )
    }

    pub(super) fn owned_seq_len(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        definition: DefId,
        arguments: &[&'tcx hir::Expr<'tcx>],
        context: Ctx,
        output: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if !self.cx.imported_seq_len(definition)
            || arguments.len() != 1
            || self.expr_ty(expression)? != Ty::nat()
        {
            return refuse(
                "owned-seq-len",
                "sequence length requires its exact live-owned pure imported signature",
                expression.span,
            );
        }
        let argument_owner = match expression.kind {
            hir::ExprKind::Call(function, _) => function.hir_id,
            hir::ExprKind::MethodCall(..) => expression.hir_id,
            _ => {
                return refuse(
                    "owned-seq-len",
                    "sequence length is not an actual native function or method call",
                    expression.span,
                );
            }
        };
        self.call_fn(
            expression,
            definition,
            self.typeck.node_args(argument_owner),
            arguments,
            context,
            output,
            false,
        )
    }
}
