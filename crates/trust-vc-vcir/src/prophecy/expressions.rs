//! Prophecy effects of raw expressions, before consumer normalization.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl Checker<'_> {
    pub(super) fn expr(&mut self, expression: &Expr, outer: bool) -> bool {
        match &expression.kind {
            ExprKind::Lit(_) | ExprKind::IntegerConstant(_) => false,
            ExprKind::Read(place) | ExprKind::Old(place) => {
                self.classification(place.local, expression.span)
            }
            ExprKind::MutRefFuture(reference) | ExprKind::HasResolved(reference) => {
                self.expr(reference, outer);
                true
            }
            ExprKind::MutRefUpdate { reference, value } => {
                self.expr(reference, outer) | self.expr(value, outer)
            }
            ExprKind::Unary { arg, .. }
            | ExprKind::Cast { arg, .. }
            | ExprKind::Borrow(arg)
            | ExprKind::MutRefCurrent(arg) => self.expr(arg, outer),
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let left = self.expr(lhs, outer);
                let right_outer =
                    outer | (left && matches!(op, BinOp::And | BinOp::Or | BinOp::Implies));
                left | self.expr(rhs, right_outer)
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let condition = self.expr(cond, outer);
                let yes = self.expr(then_expr, outer | condition);
                let no = self.expr(else_expr, outer | condition);
                condition | yes | no
            }
            ExprKind::Let { local, value, body } => {
                let taint = self.expr(value, outer);
                let old = self.locals.get(local.index()).copied();
                self.declare(*local, Some(taint), outer, value.span);
                // Block result is only its tail, not discarded initializers.
                let result = self.expr(body, outer);
                if let Some(old) = old {
                    self.set(*local, old);
                }
                result
            }
            ExprKind::Call { callee, args, .. } => self.call(*callee, args, outer, expression.span),
            ExprKind::Ctor { fields, .. } | ExprKind::Tuple(fields) => self.exprs(fields, outer),
            ExprKind::IsVariant { base, .. }
            | ExprKind::Field { base, .. }
            | ExprKind::TupleField { base, .. } => self.expr(base, outer),
            ExprKind::ProofInSpec(block) => {
                self.block(block, outer);
                false
            }
            ExprKind::ProofInSpecTail { block, tail } => {
                let saved = self.statements(block, outer);
                let result = self.expr(tail, outer);
                self.restore(saved);
                result
            }
            ExprKind::Quant {
                vars,
                triggers,
                body,
                ..
            } => {
                let saved = self.bind(vars);
                // Explicit trigger terms are checked but do not taint value.
                for trigger in triggers {
                    self.exprs(trigger, outer);
                }
                let result = self.expr(body, outer);
                self.restore(saved);
                result
            }
            ExprKind::Choose {
                vars,
                triggers,
                cond,
                result,
            } => {
                let saved = self.bind(vars);
                for trigger in triggers {
                    self.exprs(trigger, outer);
                }
                let condition = self.expr(cond, outer);
                let value = self.expr(result, outer);
                self.restore(saved);
                condition | value
            }
            ExprKind::UntriggeredQuant {
                vars,
                trigger_candidates,
                body,
                ..
            } => {
                let saved = self.bind(vars);
                self.exprs(trigger_candidates, outer);
                let result = self.expr(body, outer);
                self.restore(saved);
                result
            }
            ExprKind::UntriggeredChoose {
                vars,
                trigger_candidates,
                cond,
                result,
            } => {
                let saved = self.bind(vars);
                self.exprs(trigger_candidates, outer);
                let condition = self.expr(cond, outer);
                let value = self.expr(result, outer);
                self.restore(saved);
                condition | value
            }
        }
    }
}
