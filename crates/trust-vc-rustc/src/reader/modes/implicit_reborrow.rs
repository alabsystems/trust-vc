// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native counterpart of VIR's ImplicitReborrowOrSpecRead.
use super::*;
use rustc_middle::ty::adjustment::{Adjustment, AllowTwoPhase};

impl<'a, 'tcx> Checker<'a, 'tcx> {
    pub(super) fn implicit_reborrow(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Option<Mode>> {
        if !self.cx.new_mut_ref() {
            return Ok(None);
        }
        let [Adjustment {
            kind: Adjust::Deref(DerefAdjustKind::Builtin),
            target: deref_type,
        }, Adjustment {
            kind:
                Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut {
                    allow_two_phase_borrow,
                })),
            ..
        }] = self.typeck.expr_adjustments(expression)
        else {
            return Ok(None);
        };
        let ty::Ref(_, pointee, mutability) = self.typeck.expr_ty(expression).kind() else {
            return Ok(None);
        };
        if !mutability.is_mut()
            || self
                .tcx
                .erase_and_anonymize_regions(self.typeck.expr_ty(expression))
                != self
                    .tcx
                    .erase_and_anonymize_regions(self.typeck.expr_ty_adjusted(expression))
        {
            return Ok(None);
        }
        let phase = match allow_two_phase_borrow {
            AllowTwoPhase::No => ReborrowPhase::Immediate,
            AllowTwoPhase::Yes => ReborrowPhase::TwoPhase,
        };
        let is_spec = expect == Mode::Spec || outer == Mode::Spec || self.in_pure;
        let (carrier_mode, pointee_mode, result_mode, disposition) = if is_spec {
            // Keep the preexisting Spec rule, including its raw two-phase
            // forms and original old/prophecy source classification.
            let (carrier, result) = if self.is_place_unadjusted(expression) {
                let carrier = self.place_shape(expression, outer, expect)?;
                self.record_place(expression, carrier, Mode::Spec, AccessKind::Read)?;
                (carrier, Mode::Spec)
            } else {
                let result = self.expr_kind(expression, outer, expect)?;
                (result, Mode::Spec)
            };
            (carrier, None, result, ReborrowDisposition::SpecRead)
        } else {
            if phase != ReborrowPhase::Immediate {
                return self.unknown("two-phase implicit mutable reborrow", expression.span);
            }
            if self.typeck.expr_ty(expression) != self.typeck.expr_ty_adjusted(expression)
                || *deref_type != *pointee
            {
                return self.unknown(
                    "implicit mutable reborrow with a changed pointee type",
                    expression.span,
                );
            }
            if self.is_place_unadjusted(expression) {
                self.mutable_borrow_context(expression, outer)?;
                let context = if self.block == Ghostness::Ghost {
                    join(outer, Mode::Proof)
                } else {
                    outer
                };
                // Inspect the carrier without re-entering its adjustment chain.
                let carrier =
                    self.place_shape_access(expression, outer, Mode::Exec, AccessKind::MutBorrow)?;
                let pointee = if carrier == Mode::Spec {
                    Mode::Spec
                } else {
                    Mode::Exec
                };
                if pointee == Mode::Spec {
                    return self.error(
                        expression.span,
                        "cannot take mutable borrow of ghost-mode place",
                    );
                }
                self.record_place(expression, carrier, carrier, AccessKind::MutBorrow)?;
                (
                    carrier,
                    Some(pointee),
                    join(pointee, context),
                    ReborrowDisposition::KeptPlace,
                )
            } else {
                // Nonplace &mut*Temporary(e) cancels in VIR. Check e once;
                // its syntactic borrow/block operations keep their own roles.
                let carrier = self.expr_kind(expression, outer, expect)?;
                (carrier, None, carrier, ReborrowDisposition::KeptTemporary)
            }
        };
        self.record_adjustment_detail(
            expression,
            is_spec,
            Some(ReborrowUse {
                deref_index: 0,
                borrow_index: 1,
                phase,
                disposition,
                carrier_mode,
                pointee_mode,
                result_mode,
            }),
        )?;
        Ok(Some(result_mode))
    }

    pub(super) fn mutable_borrow_context(&self, expression: &hir::Expr<'_>, outer: Mode) -> M<()> {
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
        Ok(())
    }
}
