// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A closed original-HIR fragment with no runtime or tracked value uses.
//!
//! This is a reader component. The owned verification handoff must still bind
//! its compiler context and every builtin to the actual fresh selected cohort.

use super::super::{declaration_modes, FnInfo};
use super::*;
use crate::verus_items::VerusItem;
use rustc_middle::ty::adjustment::{Adjust, AutoBorrow, AutoBorrowMutability, DerefAdjustKind};
use rustc_middle::ty::{self, TyCtxt};

pub(crate) struct Work {
    remaining: usize,
    refused: bool,
}
impl Work {
    pub(crate) fn new() -> Self {
        Self {
            remaining: 262_144,
            refused: false,
        }
    }
    fn charge(&mut self, tcx: TyCtxt<'_>, amount: usize) -> Option<()> {
        if self.refused || tcx.dcx().has_errors().is_some() {
            self.refused = true;
            return None;
        }
        match self.remaining.checked_sub(amount) {
            Some(left) => {
                self.remaining = left;
                Some(())
            }
            None => {
                self.refused = true;
                None
            }
        }
    }
}

/// Native data from this reader invocation, not an independently usable token.
/// Only a private live read constructed by ClientImports can consume it.
#[derive(Debug)]
pub(crate) struct GhostOnly {
    owner: LocalDefId,
    body: hir::BodyId,
    builtins: Vec<DefId>,
}
impl GhostOnly {
    pub(crate) fn current(&self, tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
        owner == self.owner
            && tcx.dcx().has_errors().is_none()
            && tcx
                .hir_maybe_body_owned_by(owner)
                .is_some_and(|body| body.id() == self.body && original_body(tcx, owner, body))
    }
    pub(crate) fn builtins(&self) -> &[DefId] {
        &self.builtins
    }
}

fn original_body<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, candidate: &hir::Body<'tcx>) -> bool {
    if !declaration_modes::original_body_available(tcx, owner) {
        return false;
    }
    let Some(raw) = tcx.lower_to_hir(owner).as_owner() else {
        return false;
    };
    let hir::OwnerNode::Item(item) = raw.node() else {
        return false;
    };
    let hir::ItemKind::Fn { body, .. } = &item.kind else {
        return false;
    };
    let root = tcx.local_def_id_to_hir_id(owner);
    root.owner.def_id == owner
        && root.local_id.as_u32() == 0
        && matches!(tcx.hir_node_by_def_id(owner), hir::Node::Item(current) if std::ptr::eq(current, item))
        && std::ptr::eq(raw.attrs.get(root.local_id), tcx.hir_attrs(root))
        && raw
            .nodes
            .bodies
            .get(&body.hir_id.local_id)
            .is_some_and(|original| std::ptr::eq(*original, candidate))
}

struct Walk<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    owner: LocalDefId,
    bindings: HashSet<HirId>,
    builtins: HashSet<DefId>,
    work: &'a mut Work,
}
impl<'tcx> Walk<'_, 'tcx> {
    fn charge(&mut self, n: usize) -> Option<()> {
        self.work.charge(self.cx.tcx, n)
    }
    fn plain(&self, expression: &hir::Expr<'_>) -> bool {
        self.cx.tcx.hir_attrs(expression.hir_id).is_empty()
            && self
                .cx
                .tcx
                .typeck(self.owner)
                .expr_adjustments(expression)
                .iter()
                .all(|a| {
                    matches!(
                        a.kind,
                        Adjust::Deref(DerefAdjustKind::Builtin)
                            | Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Not))
                    )
                })
    }
    fn builtin(&mut self, definition: DefId) -> Option<()> {
        // A local diagnostic item cannot stand in for a fresh selected builtin.
        if definition.is_local()
            || self.builtins.len() >= 256 && !self.builtins.contains(&definition)
        {
            return None;
        }
        self.builtins.insert(definition);
        Some(())
    }
    fn spec_callee(&mut self, definition: DefId, _span: rustc_span::Span) -> Option<()> {
        self.charge(1)?;
        let cx = self.cx;
        if let Some(imports) = &cx.imports {
            // Pay for the complete linear inventory and the sealed registry's
            // at-most256 parameter-mode copies before doing either operation.
            self.charge(imports.call_mode_lookup_work().checked_add(256)?)?;
            if imports
                .call_modes(self.cx.tcx, definition)
                .is_some_and(|signature| {
                    signature.mode == Mode::Spec
                        && signature.ret == Mode::Spec
                        && signature
                            .params
                            .iter()
                            .all(|p| p.mode == Mode::Spec && !p.mutable_reference)
                })
            {
                return Some(());
            }
        }
        if let Some(item) = self.cx.verus_item(definition) {
            if matches!(
                item,
                VerusItem::Imply
                    | VerusItem::SpecEq
                    | VerusItem::Equal
                    | VerusItem::SpecOrd(_)
                    | VerusItem::SpecArith(_)
                    | VerusItem::SpecNeg
                    | VerusItem::SpecBitwise(_)
                    | VerusItem::BuiltinArith(_)
                    | VerusItem::SpecLiteralInteger
                    | VerusItem::SpecLiteralInt
                    | VerusItem::SpecLiteralNat
                    | VerusItem::SpecCastInteger
                    | VerusItem::Chained(_)
            ) {
                return self.builtin(definition);
            }
            return None;
        }
        if let Some(local) = definition.as_local() {
            if self.cx.tcx.def_kind(local) == DefKind::Fn
                && self.cx.tcx.def_kind(self.cx.tcx.local_parent(local)) == DefKind::Mod
                && matches!(
                    self.cx.fns.get(&definition),
                    Some(FnInfo {
                        mode: Mode::Spec,
                        ..
                    })
                )
            {
                // The live handoff requires a genuine ghost component for
                // EVERY local root, including this callee. No independent
                // external-body/trait signature can satisfy that closure.
                return Some(());
            }
        }
        None
    }
    fn callee(&self, expression: &hir::Expr<'tcx>) -> Option<DefId> {
        if !self.plain(expression) {
            return None;
        }
        let hir::ExprKind::Path(ref path) = expression.kind else {
            return None;
        };
        match self
            .cx
            .tcx
            .typeck(self.owner)
            .qpath_res(path, expression.hir_id)
        {
            Res::Def(DefKind::Fn | DefKind::AssocFn, definition) => Some(definition),
            _ => None,
        }
    }
    fn expr(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth > 64 || !self.plain(expression) {
            return None;
        }
        match expression.kind {
            hir::ExprKind::Lit(_) => Some(()),
            hir::ExprKind::Path(ref path) => match self
                .cx
                .tcx
                .typeck(self.owner)
                .qpath_res(path, expression.hir_id)
            {
                Res::Local(binding) if self.bindings.contains(&binding) => Some(()),
                _ => None,
            },
            hir::ExprKind::Call(function, args) => {
                self.charge(args.len())?;
                let definition = self.callee(function)?;
                self.spec_callee(definition, expression.span)?;
                for argument in args {
                    self.expr(argument, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::MethodCall(_, receiver, args, _) => {
                self.charge(args.len().checked_add(1)?)?;
                let definition = self
                    .cx
                    .tcx
                    .typeck(self.owner)
                    .type_dependent_def_id(expression.hir_id)?;
                self.spec_callee(definition, expression.span)?;
                self.expr(receiver, depth + 1)?;
                for argument in args {
                    self.expr(argument, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::Binary(_, left, right) => {
                if let Some(definition) = self
                    .cx
                    .tcx
                    .typeck(self.owner)
                    .type_dependent_def_id(expression.hir_id)
                {
                    self.spec_callee(definition, expression.span)?;
                } else if !matches!(
                    self.cx.tcx.typeck(self.owner).expr_ty(expression).kind(),
                    ty::Bool | ty::Int(_) | ty::Uint(_)
                ) {
                    return None;
                }
                self.expr(left, depth + 1)?;
                self.expr(right, depth + 1)
            }
            hir::ExprKind::Unary(hir::UnOp::Not | hir::UnOp::Neg, value) => {
                if let Some(definition) = self
                    .cx
                    .tcx
                    .typeck(self.owner)
                    .type_dependent_def_id(expression.hir_id)
                {
                    self.spec_callee(definition, expression.span)?;
                }
                self.expr(value, depth + 1)
            }
            hir::ExprKind::Cast(value, _) | hir::ExprKind::DropTemps(value) => {
                self.expr(value, depth + 1)
            }
            hir::ExprKind::Tup(values) => {
                self.charge(values.len())?;
                for value in values {
                    self.expr(value, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::Field(value, _) => self.expr(value, depth + 1),
            hir::ExprKind::If(condition, then_value, Some(else_value)) => {
                self.expr(condition, depth + 1)?;
                self.expr(then_value, depth + 1)?;
                self.expr(else_value, depth + 1)
            }
            hir::ExprKind::Block(block, None) if block.stmts.is_empty() => match block.expr {
                Some(value) => self.expr(value, depth + 1),
                None => Some(()),
            },
            _ => None,
        }
    }
    fn assertion(&mut self, expression: &'tcx hir::Expr<'tcx>) -> Option<()> {
        self.charge(1)?;
        if !self.plain(expression) {
            return None;
        }
        let hir::ExprKind::Call(function, [condition]) = expression.kind else {
            return None;
        };
        let definition = self.callee(function)?;
        if self.cx.verus_item(definition) != Some(VerusItem::Assert) {
            return None;
        }
        self.builtin(definition)?;
        self.expr(condition, 0)
    }
}

pub(crate) fn classify<'tcx>(
    cx: &Cx<'tcx>,
    owner: LocalDefId,
    checked: &CheckedModes,
    work: &mut Work,
) -> Option<GhostOnly> {
    work.charge(cx.tcx, 1)?;
    let tcx = cx.tcx;
    if tcx.def_kind(owner) != DefKind::Fn
        || tcx.def_kind(tcx.local_parent(owner)) != DefKind::Mod
        || !declaration_modes::original_body_available(tcx, owner)
        || checked.signature.def_id != owner.to_def_id()
        || checked.signature.body_owner != owner
        || !matches!(checked.signature.mode, Mode::Proof | Mode::Spec)
        || !checked.local_declarations.is_empty()
    {
        return None;
    }
    let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
    work.charge(tcx, attributes.len())?;
    if attributes.len() > 256 {
        return None;
    }
    let attrs = attrs::item_attrs(attributes);
    if attrs.external
        || attrs.external_body
        || !attrs.unsupported.is_empty()
        || attributes
            .iter()
            .any(|a| matches!(a, Attribute::Parsed(AttributeKind::CustomMir(..))))
    {
        return None;
    }
    let typeck = tcx.typeck(owner);
    if typeck.tainted_by_errors.is_some() {
        return None;
    }
    let body = tcx.hir_body_owned_by(owner);
    if body.contract.is_some() || !original_body(tcx, owner, body) {
        return None;
    }
    work.charge(
        tcx,
        body.params
            .len()
            .checked_add(checked.signature.params.len())?,
    )?;
    if body.params.len() > 256
        || body.params.len() != checked.signature.params.len()
        || checked
            .signature
            .params
            .iter()
            .any(|p| p.declared.mode != Mode::Spec || p.mutable_reference)
    {
        return None;
    }
    let signature = typeck.liberated_fn_sigs()[tcx.local_def_id_to_hir_id(owner)];
    if signature.safety().is_unsafe() {
        return None;
    }
    let unit = signature.output().is_unit();
    if checked.signature.ret.mode != Mode::Spec
        && !(unit
            && checked.signature.ret.mode == Mode::Proof
            && matches!(checked.signature.ret.origin, ModeOrigin::ImplicitReturn))
    {
        return None;
    }
    let mut bindings = HashSet::new();
    for (parameter, modes) in body.params.iter().zip(&checked.signature.params) {
        let PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) = parameter.pat.kind
        else {
            return None;
        };
        if modes.hir_id != parameter.hir_id || !bindings.insert(binding) {
            return None;
        }
    }
    let mut walk = Walk {
        cx,
        owner,
        bindings,
        builtins: HashSet::new(),
        work,
    };
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return None;
    };
    walk.charge(block.stmts.len())?;
    match checked.signature.mode {
        Mode::Proof if unit => {
            for statement in block.stmts {
                let (hir::StmtKind::Semi(value) | hir::StmtKind::Expr(value)) = statement.kind
                else {
                    return None;
                };
                walk.assertion(value)?;
            }
            if let Some(tail) = block.expr {
                if !typeck.expr_ty(tail).is_unit() {
                    return None;
                }
                walk.expr(tail, 0)?;
            }
        }
        Mode::Spec if block.stmts.is_empty() => {
            walk.expr(block.expr?, 0)?;
        }
        _ => return None,
    }
    let mut builtins = walk.builtins.into_iter().collect::<Vec<_>>();
    builtins.sort_by_key(|definition| tcx.def_path_hash(*definition));
    Some(GhostOnly {
        owner,
        body: body.id(),
        builtins,
    })
}

#[cfg(test)]
mod tests;
