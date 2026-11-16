//! One authenticated scalar `returns` value becomes a checked postcondition.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use rustc_hir::{self as hir, def::DefKind, def_id::DefId};
use rustc_middle::ty;
use rustc_span::Span;
use std::rc::Rc;

use super::{refuse, Area, FnProblem, FnReader, Refusal, R};
use crate::messages::{self, Phase};
use crate::reader::{attrs, UserError};
use crate::verus_items::VerusItem;
use trust_vc_vcir::{BinOp, Clause, ClauseAttrs, Expr, FnRole, LocalKind, Place, Ty};

/// Private to the current reader. Neither its expression nor a saved header
/// observation is a function body, imported equation or callable permission.
pub(super) struct Value<'tcx> {
    owner: hir::def_id::LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    checked_modes: Rc<crate::reader::modes::CheckedModes<'tcx>>,
    declared_return: ty::Ty<'tcx>,
    value_type: ty::Ty<'tcx>,
    expression: Expr,
    span: Span,
}

fn scalar(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Bool | ty::Int(_) | ty::Uint(_)) || ty.is_unit()
}

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    pub(super) fn read_returns_clause(
        &mut self,
        callee: DefId,
        call: &'tcx hir::Expr<'tcx>,
        argument: &'tcx hir::Expr<'tcx>,
    ) -> R<()> {
        if self.cx.verus_item(callee) != Some(VerusItem::Returns)
            || self.callee_def_id(match call.kind {
                hir::ExprKind::Call(function, _) => function,
                _ => return refuse("returns-header", "a non-call returns header", call.span),
            }) != Some(callee)
            || call.hir_id.owner.def_id != self.body_def
            || !matches!(self.tcx.hir_node(call.hir_id), hir::Node::Expr(original)
                if std::ptr::eq(original, call))
        {
            return refuse(
                "returns-header",
                "a returns marker without its original native builtin call",
                call.span,
            );
        }
        if self.returns_clause.is_some() {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                call.span,
                messages::header::SECOND_RETURNS,
            )));
        }
        let value = match argument.kind {
            hir::ExprKind::Array([value]) => value,
            hir::ExprKind::Array(_) => {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    call.span,
                    messages::header::RETURNS_COUNT,
                )));
            }
            _ => argument,
        };
        let item = attrs::item_attrs(
            self.tcx
                .hir_attrs(self.tcx.local_def_id_to_hir_id(self.def_id)),
        );
        // Trait inheritance and external/constant proxies need their separate
        // actual-owner joins. A scalar contract must not silently supply them.
        if self.tcx.def_kind(self.def_id) != DefKind::Fn
            || self.body_def != self.def_id
            || self.inheriting
            || self.role != FnRole::Item
            || self.subst.is_some()
            || !self.type_params.is_empty()
            || self.reading_initializer
            || self.cx.constants.real(self.def_id).is_some()
            || item.external_body
            || item.decreases_by
        {
            return refuse(
                "returns-header",
                "returns outside an ordinary local scalar function",
                call.span,
            );
        }
        if self.mode_rejected {
            return refuse(
                "returns-header",
                "a returns value has a rejected native mode walk",
                call.span,
            );
        }
        let checked = self.checked_modes.as_ref().ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "returns-header",
                "a returns value lacks complete current native mode facts",
                call.span,
            ))
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
        {
            return refuse("returns-header", "a replaced native signature", call.span);
        }
        checked
            .bindings
            .checked(self.tcx, self.def_id, self.body_def)
            .and_then(|_| {
                checked
                    .availability
                    .checked(self.tcx, self.def_id, self.body_def)
            })
            .map_err(|reason| {
                FnProblem::Refused(Refusal::new("returns-header", reason, call.span))
            })?;
        let checked_modes = Rc::clone(checked);
        let native = self
            .tcx
            .fn_sig(self.def_id)
            .instantiate_identity()
            .skip_binder();
        if !scalar(native.output())
            || native.inputs().len() != self.params.len()
            || native.inputs().iter().any(|ty| !scalar(*ty))
            || self.params.iter().any(|id| self.locals[id.index()].mutable)
        {
            return refuse(
                "returns-header",
                "returns needs scalar results and immutable scalar parameters",
                call.span,
            );
        }
        // A40 checks this value in the entry state, with requires visibility
        // and pure spec-mode rules. Mutable parameters/references above stay
        // refused until an explicit native entry-state representation exists.
        self.area = Area::Returns;
        self.attr_hook(value, false)?;
        if !attrs::verus_attrs(self.tcx.hir_attrs(value.hir_id)).is_empty() {
            return refuse(
                "returns-header",
                "a returns value with additional expression attributes",
                value.span,
            );
        }
        let value_type = self.expr_rty_adj(value);
        let expression = self.spec(value)?;
        self.returns_clause = Some(Value {
            owner: self.def_id,
            body: self.tcx.hir_body_owned_by(self.body_def),
            checked_modes,
            declared_return: native.output(),
            value_type,
            expression,
            span: value.span,
        });
        Ok(())
    }

    /// Called only after the original named-ensures and spec-header checks.
    /// Thus a generated result equality cannot impose an ensures return name,
    /// and a spec function cannot acquire a definition from `returns`.
    pub(super) fn finish_returns_clause(
        &mut self,
        ensures: &mut Vec<Clause>,
        native_return: ty::Ty<'tcx>,
    ) -> R<()> {
        let Some(value) = self.returns_clause.take() else {
            return Ok(());
        };
        let result = &self.locals[self.ret.index()];
        if value.owner != self.def_id
            || !std::ptr::eq(value.body, self.tcx.hir_body_owned_by(self.body_def))
            || value.declared_return != native_return
            || !self
                .checked_modes
                .as_ref()
                .is_some_and(|current| Rc::ptr_eq(current, &value.checked_modes))
            || !self
                .cx
                .checked_modes
                .borrow()
                .get(&self.def_id)
                .is_some_and(|current| Rc::ptr_eq(current, &value.checked_modes))
            || self.vc_ty(native_return)?.as_ref() != Some(&result.ty)
            || result.kind != LocalKind::Return
        {
            return refuse("returns-header", "a replaced native result", value.span);
        }
        if value.value_type != native_return || value.expression.ty != result.ty {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                value.span,
                messages::header::RETURNS_TYPE,
            ));
            return Ok(());
        }
        if result.ty == Ty::Unit {
            // A40 omits this tautological postcondition after checking it.
            return Ok(());
        }
        let result_type = result.ty.clone();
        let at = self.sp(value.span);
        let result = Expr::read(Place::local(self.ret), result_type, at);
        ensures.push(Clause {
            expr: Expr::binary(BinOp::Eq, result, value.expression, Ty::Bool, at),
            span: at,
            attrs: ClauseAttrs::default(),
        });
        Ok(())
    }
}
