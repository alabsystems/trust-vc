//! Original binding-mode observations consumed by native value lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_ast::{BindingMode, ByRef};
use rustc_hir as hir;
use trust_vc_vcir::Mode;

use super::{Ctx, FnProblem, FnReader, R, Refusal};

impl<'tcx> FnReader<'_, 'tcx> {
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
