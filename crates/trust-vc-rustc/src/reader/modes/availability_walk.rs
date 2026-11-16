//! Record actual access contexts, without claiming native availability.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl<'tcx> Checker<'_, 'tcx> {
    fn availability_problem(&self, reason: String, span: Span) -> Stop {
        Stop::Unknown(Refusal::new(TAG_MODES_UNKNOWN, reason, span))
    }

    /// The supported HIR subset of upstream's local-rooted AfterBorrow place
    /// grammar. Every level keeps the existing attribute, adjustment and
    /// built-in dereference restrictions. The ordinary place walk then checks
    /// each actual tuple/struct field before any facts can be completed.
    pub(super) fn is_after_borrow_place(&self, expression: &hir::Expr<'_>) -> bool {
        if !self.is_place(expression) {
            return false;
        }
        match expression.kind {
            hir::ExprKind::DropTemps(inner) | hir::ExprKind::Field(inner, _) => {
                self.is_after_borrow_place(inner)
            }
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
                self.is_plain_deref(expression, inner) && self.is_after_borrow_place(inner)
            }
            hir::ExprKind::Path(ref path) => {
                matches!(
                    self.typeck.qpath_res(path, expression.hir_id),
                    Res::Local(_)
                )
            }
            _ => false,
        }
    }

    fn local_place(
        &self,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Option<(&'tcx hir::Expr<'tcx>, HirId)> {
        match expression.kind {
            hir::ExprKind::DropTemps(inner)
            | hir::ExprKind::Field(inner, _)
            | hir::ExprKind::Unary(hir::UnOp::Deref, inner) => self.local_place(inner),
            hir::ExprKind::Path(ref path) => match self.typeck.qpath_res(path, expression.hir_id) {
                Res::Local(binding) => Some((expression, binding)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn record_place(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        place_mode: Mode,
        mode: Mode,
        access: AccessKind,
    ) -> M<()> {
        let Some((local, binding)) = self.local_place(expression) else {
            return Ok(());
        };
        let binding_mode = self.var_mode(binding, local.span)?;
        // rust_to_vir_expr marks the local PATH, including mutation paths.
        // The final access mode decides whether the marked path is shadowed.
        let shadow_check = self.cx.new_mut_ref() && !self.in_old && !self.in_explicit_prophecy;
        let erased_mode = if access == AccessKind::Read {
            mode
        } else {
            binding_mode
        };
        let erasure = if erased_mode != Mode::Spec {
            VarErasure::Keep
        } else if shadow_check && binding_mode != Mode::Spec {
            VarErasure::Shadow
        } else {
            VarErasure::Erase
        };
        self.availability
            .place(
                expression,
                local,
                PlaceUse {
                    place: expression.hir_id,
                    local_use: local.hir_id,
                    binding,
                    binding_mode,
                    place_mode,
                    mode,
                    access,
                    shadow_check,
                    erasure,
                },
            )
            .map_err(|reason| self.availability_problem(reason, expression.span))
    }

    pub(super) fn record_argument(
        &mut self,
        call: &'tcx hir::Expr<'tcx>,
        argument: &'tcx hir::Expr<'tcx>,
        position: usize,
        mode: Mode,
    ) -> M<()> {
        self.availability
            .argument(call, argument, position, mode)
            .map_err(|reason| self.availability_problem(reason, argument.span))
    }

    pub(super) fn record_operation(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        place: &'tcx hir::Expr<'tcx>,
        kind: AccessKind,
        place_mode: Mode,
        mode: Mode,
    ) -> M<()> {
        self.availability
            .operation(expression, place, kind, place_mode, mode)
            .map_err(|reason| self.availability_problem(reason, expression.span))
    }

    pub(super) fn record_adjustment(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        spec_reborrow: bool,
    ) -> M<()> {
        self.record_adjustment_detail(expression, spec_reborrow, None)
    }

    pub(super) fn record_adjustment_detail(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        spec_reborrow: bool,
        reborrow: Option<ReborrowUse>,
    ) -> M<()> {
        let mut kinds = Vec::new();
        for adjustment in self.typeck.expr_adjustments(expression) {
            kinds.push(match adjustment.kind {
                Adjust::Deref(DerefAdjustKind::Builtin) => AdjustmentKind::BuiltinDeref,
                Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Not)) => {
                    AdjustmentKind::SharedBorrow
                }
                Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut { .. })) => {
                    AdjustmentKind::MutableBorrow
                }
                Adjust::NeverToAny => AdjustmentKind::NeverToAny,
                _ => return self.unknown("an unmodelled availability adjustment", expression.span),
            });
        }
        if spec_reborrow {
            kinds.push(AdjustmentKind::SpecReborrow);
        }
        if kinds.is_empty() {
            return Ok(());
        }
        self.availability
            .adjustment(expression, kinds, reborrow)
            .map_err(|reason| self.availability_problem(reason, expression.span))
    }

    pub(super) fn mut_borrow(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        place: &'tcx hir::Expr<'tcx>,
        outer: Mode,
    ) -> M<Mode> {
        if !self.cx.new_mut_ref() {
            return self.unknown("a mutable borrow in legacy reference mode", expression.span);
        }
        if self.in_assert_by {
            return self.error(
                expression.span,
                "mutable borrow is not allowed in 'assert ... by' statement",
            );
        }
        if self.in_proof_in_spec || outer == Mode::Spec {
            return self.error(
                expression.span,
                "mutable borrow is not allowed in spec context",
            );
        }
        if self.in_pure {
            return self.error(expression.span, msg::ASSIGN_IN_PURE);
        }
        // MutBorrow(None) uses the UNCOERCED place mode, even in Proof code.
        let place_mode = self.place_rec_access(place, outer, Mode::Exec, AccessKind::MutBorrow)?;
        if place_mode == Mode::Spec {
            return self.error(place.span, "cannot take mutable borrow of ghost-mode place");
        }
        self.record_place(place, place_mode, place_mode, AccessKind::MutBorrow)?;
        let context = if self.block == Ghostness::Ghost {
            join(outer, Mode::Proof)
        } else {
            outer
        };
        let mode = join(place_mode, context);
        self.record_operation(expression, place, AccessKind::MutBorrow, place_mode, mode)?;
        Ok(mode)
    }
}
