//! Proof bodies whose original compiler MIR needs no mode erasure.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use rustc_ast::{BindingMode, ByRef};
use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, HirId, PatKind};

use trust_vc_vcir::Mode;

use super::attrs::{self, VerusAttr};
use super::modes::{
    signature_modes, CheckedLocal, CheckedModes, ModeOrigin, ResolvedMode, SignatureModeResult,
    SignatureModes,
};
use super::Cx;

pub(crate) mod ghost_only;

/// Checked declarations whose ownership is retained in the original MIR.
#[derive(Debug)]
pub(super) struct NativeOwnership {
    ret: ResolvedMode,
    locals: HashMap<HirId, CheckedLocal>,
}

impl NativeOwnership {
    pub(super) fn ret_mode(&self) -> Mode {
        self.ret.mode
    }

    pub(super) fn local_mode(&self, declaration: HirId, binding: HirId) -> Option<Mode> {
        self.locals
            .get(&declaration)
            .filter(|local| local.binding == binding)
            .map(|local| local.effective)
    }
}

/// Every evaluated value use is a Proof move in both languages. This
/// classifies syntax and checked modes, never whether a value was moved:
/// canonical compiler borrow checking must still check the original root.
pub(super) fn classify(
    cx: &Cx<'_>,
    def: LocalDefId,
    checked: &CheckedModes,
) -> Option<NativeOwnership> {
    let signature = proof_signature(cx, def.to_def_id())?;
    if checked.signature.def_id != def.to_def_id()
        || checked.signature.body_owner != def
        || checked.signature.mode != signature.mode
        || checked.signature.ret.mode != signature.ret.mode
    {
        return None;
    }
    let tcx = cx.tcx;
    let typeck = tcx.typeck(def);
    let body = tcx.hir_body_owned_by(def);
    let owner = tcx.local_def_id_to_hir_id(def);
    let unit = typeck.liberated_fn_sigs()[owner].output().is_unit();
    let mut bindings = HashSet::new();
    for parameter in body.params {
        let PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) = parameter.pat.kind
        else {
            return None;
        };
        bindings.insert(binding);
    }
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return None;
    };
    let mut locals = HashMap::new();
    let mut returned = false;
    for (index, statement) in block.stmts.iter().enumerate() {
        match statement.kind {
            hir::StmtKind::Let(local) => {
                let (
                    PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None),
                    Some(init),
                    None,
                ) = (local.pat.kind, local.init, local.els)
                else {
                    return None;
                };
                let fact = checked.local_declarations.get(&local.hir_id)?;
                if fact.binding != binding
                    || fact.declared.mode != Mode::Proof
                    || fact.effective != Mode::Proof
                    || !matches!(fact.declared.origin, ModeOrigin::Attribute(_))
                    || typeck
                        .pat_adjustments()
                        .get(local.pat.hir_id)
                        .is_some_and(|adjustments| !adjustments.is_empty())
                    || typeck
                        .pat_binding_modes()
                        .get(binding)
                        .is_some_and(|mode| matches!(mode, BindingMode(ByRef::Yes(..), _)))
                    || matches!(typeck.pat_ty(local.pat).kind(), rustc_middle::ty::Ref(..))
                    || attrs::verus_attrs(tcx.hir_attrs(local.hir_id))
                        .iter()
                        .any(|(attr, _)| {
                            !matches!(attr, VerusAttr::Mode(_) | VerusAttr::LetMarker(_))
                        })
                    || !proof_value(cx, def, init, &bindings)
                {
                    return None;
                }
                // The initializer resolves old bindings, including a name
                // shadowed by this declaration.
                bindings.insert(binding);
                locals.insert(local.hir_id, *fact);
            }
            hir::StmtKind::Semi(expression) | hir::StmtKind::Expr(expression) => {
                if let hir::ExprKind::Ret(value) = expression.kind {
                    if index + 1 != block.stmts.len()
                        || block.expr.is_some()
                        || !plain_expression(cx, def, expression)
                        || value.is_none() && !unit
                        || value.is_some_and(|value| !proof_value(cx, def, value, &bindings))
                    {
                        return None;
                    }
                    returned = true;
                } else if !proof_call(cx, def, expression, &bindings) {
                    return None;
                }
            }
            hir::StmtKind::Item(_) => return None,
        }
    }
    if block
        .expr
        .is_some_and(|tail| !proof_value(cx, def, tail, &bindings))
    {
        return None;
    }
    if !unit && block.expr.is_none() && !returned {
        return None;
    }
    if signature.params.is_empty() && locals.is_empty() && unit {
        return None;
    }
    Some(NativeOwnership {
        ret: checked.signature.ret,
        locals,
    })
}

/// A free Proof signature with only plain tracked value parameters and a
/// Proof value result. Shared elaboration supplies all modes and origins.
fn proof_signature(cx: &Cx<'_>, def: DefId) -> Option<SignatureModes> {
    let tcx = cx.tcx;
    let local = def.as_local()?;
    if tcx.def_kind(def) != DefKind::Fn
        || tcx.def_kind(tcx.local_parent(local)) != DefKind::Mod
        || tcx.is_typeck_child(def)
    {
        return None;
    }
    let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(local));
    // Injected MIR can bypass native borrow checking and does not represent
    // the HIR body whose modes established this fragment.
    if attributes
        .iter()
        .any(|attribute| matches!(attribute, Attribute::Parsed(AttributeKind::CustomMir(..))))
    {
        return None;
    }
    let attr = attrs::item_attrs(attributes);
    if attr.external || attr.external_body || !attr.unsupported.is_empty() {
        return None;
    }
    let SignatureModeResult::Known(signature) = signature_modes(cx, def, tcx.def_span(def)) else {
        return None;
    };
    if signature.body_owner != local
        || signature.mode != Mode::Proof
        || signature.ret.mode != Mode::Proof
        || signature
            .params
            .iter()
            .any(|parameter| parameter.declared.mode != Mode::Proof || parameter.mutable_reference)
    {
        return None;
    }
    let body = tcx.hir_body_owned_by(local);
    let typeck = tcx.typeck(local);
    let owner = tcx.local_def_id_to_hir_id(local);
    if matches!(
        typeck.liberated_fn_sigs()[owner].output().kind(),
        rustc_middle::ty::Ref(..)
    ) || body.params.iter().any(|parameter| {
        !matches!(
            parameter.pat.kind,
            PatKind::Binding(BindingMode(ByRef::No, _), _, _, None)
        ) || matches!(
            typeck.pat_ty(parameter.pat).kind(),
            rustc_middle::ty::Ref(..)
        )
    }) {
        return None;
    }
    Some(signature)
}

fn plain_expression(cx: &Cx<'_>, owner: LocalDefId, expression: &hir::Expr<'_>) -> bool {
    attrs::verus_attrs(cx.tcx.hir_attrs(expression.hir_id)).is_empty()
        && cx.tcx.typeck(owner).expr_adjustments(expression).is_empty()
}

fn proof_value(
    cx: &Cx<'_>,
    owner: LocalDefId,
    expression: &hir::Expr<'_>,
    bindings: &HashSet<HirId>,
) -> bool {
    if !plain_expression(cx, owner, expression) {
        return false;
    }
    match expression.kind {
        hir::ExprKind::Path(ref path) => {
            matches!(cx.tcx.typeck(owner).qpath_res(path, expression.hir_id),
                Res::Local(binding) if bindings.contains(&binding))
        }
        hir::ExprKind::Call(..) => proof_call(cx, owner, expression, bindings),
        _ => false,
    }
}

fn proof_call(
    cx: &Cx<'_>,
    owner: LocalDefId,
    expression: &hir::Expr<'_>,
    bindings: &HashSet<HirId>,
) -> bool {
    if !plain_expression(cx, owner, expression) {
        return false;
    }
    let hir::ExprKind::Call(function, arguments) = expression.kind else {
        return false;
    };
    if !plain_expression(cx, owner, function) {
        return false;
    }
    let hir::ExprKind::Path(ref path) = function.kind else {
        return false;
    };
    let Res::Def(DefKind::Fn, callee) = cx.tcx.typeck(owner).qpath_res(path, function.hir_id)
    else {
        return false;
    };
    let Some(signature) = proof_signature(cx, callee) else {
        return false;
    };
    arguments.len() == signature.params.len()
        && arguments
            .iter()
            .all(|argument| proof_value(cx, owner, argument, bindings))
}
