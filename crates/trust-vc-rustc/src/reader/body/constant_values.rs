//! Current native value reads and independently checked executable initializers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
use super::*;

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    pub(super) fn checked_initializer(&self) -> R<()> {
        let span = self.tcx.def_span(self.def_id);
        let refuse =
            |detail| FnProblem::Refused(Refusal::new("constant-initializer", detail, span));
        let facts = self.checked_modes.as_ref().ok_or_else(|| {
            refuse("an executable initializer needs the complete original native mode walk")
        })?;
        if !self.cx.constants.current_pair(self.tcx, self.def_id)
            || self.body_def != self.def_id
            || !self
                .cx
                .checked_modes
                .borrow()
                .get(&self.def_id)
                .is_some_and(|current| std::rc::Rc::ptr_eq(current, facts))
            || facts.signature.def_id != self.def_id.to_def_id()
            || facts.signature.body_owner != self.body_def
            || facts.signature.mode != Mode::Exec
            || facts.signature.ret.mode != Mode::Exec
            || !facts.signature.params.is_empty()
        {
            return Err(refuse(
                "the initializer pair/signature is not this current completed body",
            ));
        }
        facts
            .availability
            .checked(self.tcx, self.def_id, self.body_def)
            .map_err(|_| refuse("the initializer's original availability facts are unavailable"))?;
        // This deliberately does NOT create NativeOwnership. Tracked locals,
        // ghost result erasure and unrepresented ownership remain subject to
        // their existing producer/real erased-program gates.
        Ok(())
    }

    pub(super) fn checked_constant_use(
        &self,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> R<Option<super::super::constants::Use<'tcx>>> {
        let selected = self
            .cx
            .constants
            .select(self.tcx, self.body_def, self.typeck, expression)
            .map_err(|reason| {
                FnProblem::Refused(Refusal::new("constant-use", reason, expression.span))
            })?;
        let Some(selected) = selected else {
            return Ok(None);
        };
        let refuse =
            |detail| FnProblem::Refused(Refusal::new("constant-use", detail, expression.span));
        let facts = self.checked_modes.as_ref().ok_or_else(|| {
            FnProblem::MissingConstantModes(Refusal::new(
                "constant-use",
                "the constant occurrence lacks a complete original native mode walk",
                expression.span,
            ))
        })?;
        if !self
            .cx
            .checked_modes
            .borrow()
            .get(&self.def_id)
            .is_some_and(|current| std::rc::Rc::ptr_eq(current, facts))
            || !facts
                .constant_uses
                .get(&expression.hir_id)
                .is_some_and(|observed| observed.same_selection(&selected))
        {
            return Err(refuse(
                "the value/call is not this body's canonical native selection",
            ));
        }
        facts
            .availability
            .checked(self.tcx, self.def_id, self.body_def)
            .map_err(|_| refuse("the constant occurrence lost original availability facts"))?;
        Ok(Some(selected))
    }

    pub(super) fn emit_value_call(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        target: Target,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if target.mode != Mode::Exec || target.ret_mode != Some(Mode::Exec) {
            return refuse(
                "constant-use",
                "an executable value read changed result mode",
                expression.span,
            );
        }
        let result_type = self.expr_ty(expression)?;
        let dest = self.temp_with_mode(result_type, Mode::Exec, expression.span);
        out.push(Stmt::new(
            self.sp(expression.span),
            StmtKind::Let {
                local: dest,
                init: None,
            },
        ));
        let site = self.site();
        out.push(Stmt::new(
            self.sp(expression.span),
            StmtKind::Call {
                callee: target.id,
                type_args: target.type_args,
                args: Vec::new(),
                dest: Some(Place::local(dest)),
                site,
            },
        ));
        Ok(self.read_local(dest, expression.span))
    }
}
