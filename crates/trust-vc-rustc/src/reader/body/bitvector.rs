//! The pinned one-block assert query, without the function-header side effects.

use rustc_hir as hir;
use trust_vc_vcir::{Clause, Stmt, StmtKind};

use super::{attrs, refuse, Ctx, FnProblem, FnReader, Phase, UserError, VerusAttr, VerusItem, R};

/// The SST result distinction, before statement-position lowering discards a
/// value. In particular, an explicit unit value is not an implicit unit.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TailValue {
    Explicit,
    ImplicitUnit,
    Never,
}

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn assert_bitvector_by(
        &mut self,
        call: &'tcx hir::Expr<'tcx>,
        proof: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        if ctx == Ctx::Exec && !self.mode_rejected {
            return refuse(
                "assert-bitvector",
                "an isolated BV assertion in exec code",
                call.span,
            );
        }
        for (attr, at) in attrs::verus_attrs(self.tcx.hir_attrs(call.hir_id)) {
            if attr == VerusAttr::SpinoffProver {
                return Err(FnProblem::Rejected(UserError::new(Phase::RustToVir, at,
                    "#[verifier::spinoff_prover] is implied for assert by nonlinear_arith and assert by bit_vector")));
            }
            return refuse(
                "assert-bitvector-attribute",
                "an unsupported attribute on an isolated BV assertion",
                at,
            );
        }
        let hir::ExprKind::Block(block, None) = proof.kind else {
            return refuse(
                "assert-bitvector",
                "an isolated BV assertion whose argument is not a block",
                proof.span,
            );
        };
        let mut seen = Vec::new();
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut consumed = 0;
        for statement in block.stmts {
            let (hir::StmtKind::Semi(expr) | hir::StmtKind::Expr(expr)) = statement.kind else {
                break;
            };
            if !self.bitvector_header(expr, &mut seen, &mut requires, &mut ensures)? {
                break;
            }
            consumed += 1;
        }
        let tail_is_header = consumed == block.stmts.len()
            && match block.expr {
                Some(tail) => {
                    self.bitvector_header(tail, &mut seen, &mut requires, &mut ensures)?
                }
                None => false,
            };
        if ensures.is_empty() {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                call.span,
                "assert_nonlinear_by/assert_bitvector_by must have at least one ensures",
            )));
        }
        // Still read every residual expression for the original language and
        // attribute checks. Its effects never become the surrounding proof.
        let mut residual = Vec::new();
        for statement in &block.stmts[consumed..] {
            self.stmt(statement, Ctx::Proof, &mut residual)?;
        }
        let tail = if tail_is_header { None } else { block.expr };
        if let Some(tail) = tail {
            self.stmt_expr(tail, Ctx::Proof, &mut residual)?;
        }
        let explicit_value =
            self.bitvector_block_value(&block.stmts[consumed..], tail) == TailValue::Explicit;
        // An implicit-unit tail still has its SST statement (including an
        // empty nested block). Only the consumed requires/ensures tail has no
        // residual expression. Do not let VcIR's discarded-unit optimization
        // erase this language check.
        if tail.is_some() || !residual.is_empty() {
            self.errors.push(UserError::new(
                Phase::Sst,
                call.span,
                if explicit_value {
                    "assert_bitvector_by cannot contain a return value"
                } else {
                    "assert_bitvector_by cannot contain a proof block"
                },
            ));
        }
        let site = self.site();
        out.push(Stmt::new(
            self.sp(call.span),
            StmtKind::AssertBitVector {
                requires,
                ensures,
                architecture: self.cx.architecture,
                site,
            },
        ));
        Ok(())
    }

    /// A block stops producing a value at its first never-returning statement,
    /// including a declaration whose real initializer never returns. Keep one
    /// result walk for the outer residual block and every nested block.
    fn bitvector_block_value(
        &self,
        statements: &'tcx [hir::Stmt<'tcx>],
        tail: Option<&'tcx hir::Expr<'tcx>>,
    ) -> TailValue {
        for statement in statements {
            let expression = match statement.kind {
                hir::StmtKind::Semi(expr) | hir::StmtKind::Expr(expr) => Some(expr),
                hir::StmtKind::Let(local) => local.init,
                hir::StmtKind::Item(_) => None,
            };
            if expression.is_some_and(|expr| self.bitvector_tail_value(expr) == TailValue::Never) {
                return TailValue::Never;
            }
        }
        tail.map_or(TailValue::ImplicitUnit, |expr| {
            self.bitvector_tail_value(expr)
        })
    }

    /// Classify an already-read native expression as `expr_to_stm_opt` does.
    /// This only selects a diagnostic; every operand/effect/attribute was read
    /// above, and every residual tail is rejected regardless of this result.
    fn bitvector_tail_value(&self, expr: &'tcx hir::Expr<'tcx>) -> TailValue {
        if self.typeck.expr_ty(expr).is_never() || self.never_to_any(expr) {
            return TailValue::Never;
        }
        match expr.kind {
            hir::ExprKind::DropTemps(inner) => self.bitvector_tail_value(inner),
            hir::ExprKind::Block(block, None) => {
                self.bitvector_block_value(block.stmts, block.expr)
            }
            hir::ExprKind::If(condition, then_expr, else_expr) => {
                if self.bitvector_tail_value(condition) == TailValue::Never {
                    return TailValue::Never;
                }
                let left = self.bitvector_tail_value(then_expr);
                let right = else_expr.map_or(TailValue::ImplicitUnit, |expr| {
                    self.bitvector_tail_value(expr)
                });
                match (left, right) {
                    (TailValue::ImplicitUnit, _) | (_, TailValue::ImplicitUnit) => {
                        TailValue::ImplicitUnit
                    }
                    (TailValue::Never, other) | (other, TailValue::Never) => other,
                    _ => TailValue::Explicit,
                }
            }
            hir::ExprKind::Call(function, [condition, _])
                if self
                    .callee_item(function)
                    .is_some_and(|(item, _)| item == VerusItem::Imply) =>
            {
                // The authenticated implication marker lowers as !left ||
                // right, not a strict call. Its right side may never execute.
                if self.bitvector_tail_value(condition) == TailValue::Never {
                    TailValue::Never
                } else {
                    TailValue::Explicit
                }
            }
            hir::ExprKind::Call(function, arguments) => {
                if arguments
                    .iter()
                    .any(|argument| self.bitvector_tail_value(argument) == TailValue::Never)
                {
                    TailValue::Never
                } else if self.is_struct_ctor(function) {
                    TailValue::Explicit
                } else {
                    self.bitvector_call_value(expr, self.callee_def_id(function))
                }
            }
            hir::ExprKind::MethodCall(_, receiver, arguments, _) => {
                if self.bitvector_tail_value(receiver) == TailValue::Never
                    || arguments
                        .iter()
                        .any(|argument| self.bitvector_tail_value(argument) == TailValue::Never)
                {
                    TailValue::Never
                } else {
                    self.bitvector_call_value(expr, self.typeck.type_dependent_def_id(expr.hir_id))
                }
            }
            hir::ExprKind::Tup(elements) => {
                if elements
                    .iter()
                    .any(|element| self.bitvector_tail_value(element) == TailValue::Never)
                {
                    TailValue::Never
                } else {
                    TailValue::Explicit
                }
            }
            hir::ExprKind::Unary(_, inner)
            | hir::ExprKind::Cast(inner, _)
            | hir::ExprKind::AddrOf(_, _, inner)
            | hir::ExprKind::Field(inner, _) => {
                if self.bitvector_tail_value(inner) == TailValue::Never {
                    TailValue::Never
                } else {
                    TailValue::Explicit
                }
            }
            hir::ExprKind::Binary(operator, left, right) => {
                if self.bitvector_tail_value(left) == TailValue::Never
                    || (!matches!(operator.node, hir::BinOpKind::And | hir::BinOpKind::Or)
                        && self.bitvector_tail_value(right) == TailValue::Never)
                {
                    TailValue::Never
                } else {
                    // A lazy operator retains its other, value-producing
                    // branch even if the conditionally evaluated side diverges.
                    TailValue::Explicit
                }
            }
            hir::ExprKind::Struct(_, fields, base) => {
                if fields
                    .iter()
                    .any(|field| self.bitvector_tail_value(field.expr) == TailValue::Never)
                    || matches!(base, hir::StructTailExpr::Base(expr)
                        if self.bitvector_tail_value(expr) == TailValue::Never)
                {
                    TailValue::Never
                } else {
                    TailValue::Explicit
                }
            }
            hir::ExprKind::Assign(left, right, _) | hir::ExprKind::AssignOp(_, left, right) => {
                if self.bitvector_tail_value(left) == TailValue::Never
                    || self.bitvector_tail_value(right) == TailValue::Never
                {
                    TailValue::Never
                } else {
                    TailValue::ImplicitUnit
                }
            }
            hir::ExprKind::Loop(..) => TailValue::ImplicitUnit,
            hir::ExprKind::Ret(..) | hir::ExprKind::Break(..) | hir::ExprKind::Continue(..) => {
                TailValue::Never
            }
            // Tuples (including ()), paths, constructors and other read values
            // remain explicit even when their native result type is unit.
            _ => TailValue::Explicit,
        }
    }

    fn bitvector_call_value(
        &self,
        expr: &'tcx hir::Expr<'tcx>,
        definition: Option<rustc_hir::def_id::DefId>,
    ) -> TailValue {
        let Some(definition) = definition else {
            // An unresolved call cannot reach here after successful lowering.
            // Keep an explicit result instead of silently accepting its tail.
            return TailValue::Explicit;
        };
        match self.cx.verus_item(definition) {
            Some(
                VerusItem::Assert
                | VerusItem::Assume
                | VerusItem::Admit
                | VerusItem::AssertBy
                | VerusItem::AssertBitvectorBy
                | VerusItem::AssertForallBy
                | VerusItem::RevealHide,
            ) => TailValue::ImplicitUnit,
            Some(_) => TailValue::Explicit,
            None if self
                .cx
                .fns
                .get(&definition)
                .is_some_and(|info| info.mode == trust_vc_vcir::Mode::Spec)
                || !self.typeck.expr_ty(expr).is_unit() =>
            {
                TailValue::Explicit
            }
            None => TailValue::ImplicitUnit,
        }
    }

    fn bitvector_header(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        seen: &mut Vec<VerusItem>,
        requires: &mut Vec<Clause>,
        ensures: &mut Vec<Clause>,
    ) -> R<bool> {
        let hir::ExprKind::Call(function, arguments) = expr.kind else {
            return Ok(false);
        };
        let Some((item, _)) = self.callee_item(function) else {
            return Ok(false);
        };
        if !matches!(item, VerusItem::Requires | VerusItem::Ensures) {
            if item.is_header() {
                return refuse(
                    "assert-bitvector-header",
                    "a header other than requires or ensures in an isolated BV assertion",
                    expr.span,
                );
            }
            return Ok(false);
        }
        self.attr_hook(expr, false)?;
        if seen.contains(&item) {
            if let Some(message) = crate::messages::header::second_call(item) {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    expr.span,
                    message,
                )));
            }
        }
        seen.push(item);
        let [argument] = arguments else {
            return refuse(
                "assert-bitvector-header",
                "a BV header call without one argument",
                expr.span,
            );
        };
        if matches!(argument.kind, hir::ExprKind::Closure(_)) {
            return refuse(
                "assert-bitvector-header",
                "an isolated BV ensures with a return-value binder",
                argument.span,
            );
        }
        let clauses = self.clause_list(argument, item)?;
        if item == VerusItem::Requires {
            requires.extend(clauses);
        } else {
            ensures.extend(clauses);
        }
        self.attr_hook(expr, true)?;
        Ok(true)
    }
}
