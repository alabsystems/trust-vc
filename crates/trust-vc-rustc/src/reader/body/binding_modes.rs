//! Original binding-mode observations consumed by native value lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_ast::{BindingMode, ByRef};
use rustc_hir as hir;
use trust_vc_vcir::{DeclProphecy, Expr, Mode, Place, Stmt, StmtKind, Ty};

use super::{Ctx, FnProblem, FnReader, Refusal, R};

impl<'tcx> FnReader<'_, 'tcx> {
    /// Join this exact original occurrence to its completed native context.
    /// Physical executable syntax is distinct from the logical outer and
    /// result modes; legacy Spec values may still contain machine checks.
    fn legacy_native_value_modes(
        &self,
        source: &'tcx hir::Expr<'tcx>,
        value_ty: &Ty,
        ctx: Ctx,
        expected: Option<Mode>,
    ) -> R<Option<(Mode, Mode)>> {
        if self.mode_rejected
            || ctx != Ctx::Exec
            || !self.cx.legacy_functions.contains(&self.def_id)
            || !self.cx.native_ownership.borrow().contains_key(&self.def_id)
        {
            // No checked-evaluation form is authorized here. Unsupported
            // ownership still reaches read_fn's mandatory legacy-erasure
            // gate, preserving the ordinary refusal and error precedence.
            return Ok(None);
        }
        let fail =
            |detail| FnProblem::Refused(Refusal::new("legacy-initializer", detail, source.span));
        let checked = self
            .checked_modes
            .as_ref()
            .ok_or_else(|| fail("a legacy value lacks completed native modes".to_string()))?;
        if !self
            .cx
            .checked_modes
            .borrow()
            .get(&self.def_id)
            .is_some_and(|actual| std::rc::Rc::ptr_eq(actual, checked))
            || !checked
                .legacy_context(self.cx, self.def_id, self.body_def)
                .map_err(fail)?
        {
            return Err(fail(
                "a legacy value lost its canonical current language/mode facts".into(),
            ));
        }
        let facts = checked
            .expressions
            .for_expression(self.tcx, self.def_id, self.body_def, source)
            .map_err(fail)?;
        if !facts.iter().any(|row| {
            std::ptr::eq(row.expression, source)
                && expected.is_none_or(|expected| row.context.expected == expected)
        }) {
            return Err(fail(
                "a legacy value lacks its actual expected source context".into(),
            ));
        }
        let mut observations = facts.iter().filter(|row| {
            std::ptr::eq(row.expression, source)
                && expected.is_none_or(|expected| row.context.expected == expected)
                && !row.context.pure
                && !row.context.proof_in_spec
                && !row.context.assert_by
                && !row.context.block_ghost
                && !row.context.uses_ghost_blocks
        });
        let Some(actual) = observations.next() else {
            // Pure assertion operands and explicit ghost/proof contexts keep
            // their existing expression lowering. Their known native context
            // is not permission to emit physical-Exec evaluation forms.
            return Ok(None);
        };
        if observations.next().is_some()
            || (self.vc_ty(actual.native_type)?.as_ref() != Some(value_ty)
                && self.vc_ty(actual.adjusted_type)?.as_ref() != Some(value_ty))
        {
            return Err(fail(
                "a legacy value lost its unique current source/type join".into(),
            ));
        }
        Ok(Some((actual.result, actual.context.expected)))
    }

    fn legacy_value_context(
        &self,
        source: &'tcx hir::Expr<'tcx>,
        ty: &Ty,
        ctx: Ctx,
        expected: Option<Mode>,
    ) -> R<Option<Mode>> {
        // Saving for a Spec consumer must retain raw prophecy, including an
        // Exec-valued conditional with a Spec condition. Native result mode
        // alone does not describe that value's entire observation context.
        Ok(self
            .legacy_native_value_modes(source, ty, ctx, expected)?
            .map(|(result, expected)| match (result, expected) {
                (Mode::Spec, _) | (_, Mode::Spec) => Mode::Spec,
                (Mode::Proof, _) | (_, Mode::Proof) => Mode::Proof,
                _ => Mode::Exec,
            }))
    }

    pub(super) fn legacy_spec_condition(&self, source: &'tcx hir::Expr<'tcx>, ctx: Ctx) -> R<bool> {
        // Match the exact condition occurrence used by native if_expr;
        // its one DropTemps wrapper has no separate logical value mode.
        let source = match source.kind {
            hir::ExprKind::DropTemps(inner) => inner,
            _ => source,
        };
        Ok(self
            .legacy_native_value_modes(source, &Ty::Bool, ctx, None)?
            .is_some_and(|(result, _)| result == Mode::Spec))
    }

    /// Save one value without changing the destination's declared mode or
    /// prophecy. This statement authorizes only its own expression checks;
    /// it supplies no native ownership or executable-value permission.
    pub(super) fn legacy_value_declaration(
        &self,
        local: trust_vc_vcir::LocalId,
        value: Expr,
        source: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        expected: Option<Mode>,
    ) -> R<StmtKind> {
        if self.locals[local.index()].mode == Mode::Spec
            && self
                .legacy_value_context(source, &value.ty, ctx, expected)?
                .is_some()
        {
            Ok(StmtKind::LetChecked { local, init: value })
        } else {
            Ok(StmtKind::Let {
                local,
                init: Some(value),
            })
        }
    }

    pub(super) fn legacy_saved_value_mode(
        &self,
        source: &'tcx hir::Expr<'tcx>,
        value: &Expr,
        ctx: Ctx,
    ) -> R<Mode> {
        Ok(self
            .legacy_value_context(source, &value.ty, ctx, None)?
            .unwrap_or_else(|| self.operand_mode(value, ctx)))
    }

    pub(super) fn legacy_result_mode(
        &self,
        source: &'tcx hir::Expr<'tcx>,
        ty: &Ty,
        ctx: Ctx,
    ) -> R<Mode> {
        Ok(match self.legacy_value_context(source, ty, ctx, None)? {
            Some(Mode::Exec) => Mode::Exec,
            // Physical Exec assignments cannot target a Proof local. A
            // generated Spec save retains the producer's raw mode and Unit
            // prophecy through the existing DelayedInfer origin machinery.
            Some(Mode::Proof | Mode::Spec) => Mode::Spec,
            None => ctx.local_mode(),
        })
    }

    /// A branch assignment cannot carry executable checks into Spec storage.
    /// Save its value at the actual branch point, preserving raw prophecy,
    /// and let the ordinary assignment transport only that saved observation.
    pub(super) fn legacy_branch_value(
        &mut self,
        source: &'tcx hir::Expr<'tcx>,
        value: Expr,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let Some(Mode::Spec) = self.legacy_value_context(source, &value.ty, ctx, None)? else {
            return Ok(value);
        };
        let local = self.temp_with_mode(value.ty.clone(), Mode::Spec, source.span);
        self.locals[local.index()].prophecy = DeclProphecy::DelayedInfer;
        out.push(Stmt::new(
            self.sp(source.span),
            StmtKind::LetChecked { local, init: value },
        ));
        Ok(self.read_local(local, source.span))
    }

    /// Authenticate the physical evaluation and logical Spec-store effect
    /// of one actual native assignment. The caller retains its exact RHS in
    /// AssignSpec, preserving raw prophecy separately from surrounding control.
    pub(super) fn legacy_spec_assignment(
        &self,
        source: &'tcx hir::Expr<'tcx>,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        place: &Place,
        value: &Expr,
        ctx: Ctx,
    ) -> R<bool> {
        if self.mode_rejected
            || ctx != Ctx::Exec
            || !self.cx.legacy_functions.contains(&self.def_id)
            || place.has_deref()
            || self
                .locals
                .get(place.local.index())
                .is_none_or(|local| local.mode != Mode::Spec)
        {
            return Ok(false);
        }
        if self
            .legacy_native_value_modes(rhs, &value.ty, ctx, Some(Mode::Spec))?
            .is_none()
        {
            return Ok(false);
        }
        let fail =
            |detail| FnProblem::Refused(Refusal::new("legacy-assignment", detail, source.span));
        let checked = self
            .checked_modes
            .as_ref()
            .ok_or_else(|| fail("missing native assignment modes".into()))?;
        // The canonical original-MIR producer already validated the whole
        // immutable inventory. Rejoin this native allocation and indexed
        // occurrences without rescanning the function for each assignment.
        checked
            .availability
            .in_context(self.tcx, self.def_id, self.body_def)
            .map_err(fail)?;
        let operation = checked.availability.operation_for(source).map_err(fail)?;
        let access = checked
            .availability
            .use_for(lhs, super::super::modes::AccessKind::Assign)
            .map_err(fail)?;
        if operation.expression != source.hir_id
            || operation.place != lhs.hir_id
            || operation.kind != super::super::modes::AccessKind::Assign
            || operation.mode != Mode::Spec
            || operation.place_mode != Mode::Spec
            || access.mode != Mode::Spec
            || access.place_mode != Mode::Spec
            || access.place != lhs.hir_id
            || self.local_ids.get(&access.binding) != Some(&place.local)
            || self.expr_ty(lhs)? != value.ty
        {
            return Err(fail(
                "a Spec assignment lost its exact native operation/place/type join".into(),
            ));
        }
        Ok(true)
    }

    pub(super) fn checked_legacy_context(&self) -> R<()> {
        let fail = |detail| FnProblem::Refused(Refusal::new("legacy-modes", detail, self.sig_span));
        let checked = self
            .checked_modes
            .as_ref()
            .ok_or_else(|| fail("legacy source lacks a completed native mode walk".to_string()))?;
        if !self
            .cx
            .checked_modes
            .borrow()
            .get(&self.def_id)
            .is_some_and(|actual| std::rc::Rc::ptr_eq(actual, checked))
        {
            return Err(fail(
                "legacy source lost its canonical completed mode Rc".into(),
            ));
        }
        if !checked
            .legacy_context(self.cx, self.def_id, self.body_def)
            .map_err(fail)?
        {
            return Err(fail("source does not have a legacy native context".into()));
        }
        checked
            .availability
            .checked(self.tcx, self.def_id, self.body_def)
            .map_err(fail)?;
        Ok(())
    }

    /// Inference establishes a value mode, not a tracked ownership receipt.
    /// Only the original canonical uninitialized declaration can consume it.
    pub(super) fn checked_inferred_value_mode(&self, local: &hir::LetStmt<'tcx>) -> R<Mode> {
        if self.mode_rejected
            || local.init.is_some()
            || local.els.is_some()
            || local.hir_id.owner.def_id != self.body_def
            || !matches!(self.tcx.hir_node(local.hir_id), hir::Node::LetStmt(original) if std::ptr::eq(original, local))
            || !matches!(
                local.pat.kind,
                hir::PatKind::Binding(BindingMode(ByRef::No, _), _, _, None)
            )
        {
            return Err(FnProblem::Refused(Refusal::new(
                "infer-mode",
                "mode inference requires an original plain uninitialized binding",
                local.span,
            )));
        }
        let mode = self.checked_binding_mode(local.pat, Ctx::Exec)?;
        match mode {
            Mode::Exec | Mode::Spec => Ok(mode),
            Mode::Proof => Err(FnProblem::Refused(Refusal::new(
                "infer-mode-ownership",
                "an inferred proof binding requires a native ownership receipt",
                local.span,
            ))),
        }
    }

    /// Rejected functions are read solely for earlier-phase diagnostics.
    /// Admitted bindings require their completed original-HIR observation.
    pub(super) fn checked_binding_mode(&self, pat: &hir::Pat<'tcx>, ctx: Ctx) -> R<Mode> {
        if self.mode_rejected {
            return Ok(ctx.local_mode());
        }
        if let Some(mode) = self.header_binding_scopes.mode_for(self, pat) {
            return mode;
        }
        let facts = self.checked_modes.as_ref().ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "binding-modes",
                "a native binding lacks a completed mode walk",
                pat.span,
            ))
        })?;
        facts
            .bindings
            .mode_for(
                self.tcx,
                self.def_id,
                self.body_def,
                self.tcx.hir_body_owned_by(self.body_def),
                pat,
            )
            .map_err(|reason| FnProblem::Refused(Refusal::new("binding-modes", reason, pat.span)))
    }
}
