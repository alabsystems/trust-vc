// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Closed original getter schema; no helper names participate in admission.

extern crate rustc_abi;

use rustc_ast::{BindingMode, ByRef, LitKind};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Slot {
    pub(super) nominal: NativeKey,
    pub(super) variant: u32,
    pub(super) field: u32,
}

pub(super) struct Helper {
    pub(super) owner: LocalDefId,
    pub(super) slot: Slot,
}

fn literal(expression: &hir::Expr<'_>) -> Option<Symbol> {
    let hir::ExprKind::Lit(value) = expression.kind else {
        return None;
    };
    let LitKind::Str(value, _) = value.node else {
        return None;
    };
    Some(value)
}

fn body<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    work: &mut Work,
) -> Result<(&'tcx hir::Body<'tcx>, hir::HirId), Failure> {
    let raw = tcx
        .lower_to_hir(owner)
        .as_owner()
        .ok_or_else(|| Failure::Unknown("the helper has no original owner".into()))?;
    work.charge(tcx, raw.nodes.nodes.len() + raw.attrs.map.len())?;
    for (_, attributes) in raw.attrs.map.iter() {
        work.charge(tcx, attributes.len())?;
    }
    if !raw.parenting.is_empty()
        || !raw.children.is_empty()
        || raw.nodes.bodies.len() != 1
        || raw.attrs.define_opaque.is_some()
        || raw
            .attrs
            .map
            .iter()
            .any(|(id, _)| *id != hir::ItemLocalId::ZERO)
    {
        return Err(Failure::Unknown(
            "the getter has nested owners, contracts or unrepresented attributes".into(),
        ));
    }
    let OwnerNode::ImplItem(item) = raw.node() else {
        return Err(Failure::Unknown(
            "a synthesized getter is not an inherent member".into(),
        ));
    };
    let hir::ImplItemKind::Fn(signature, body_id) = item.kind else {
        return Err(Failure::Unknown(
            "a synthesized member is not a getter function".into(),
        ));
    };
    if !item.generics.params.is_empty()
        || !item.generics.predicates.is_empty()
        || signature.decl.inputs.len() != 1
        || signature.decl.c_variadic()
        || !signature.header.is_safe()
        || signature.header.is_async()
        || !matches!(signature.header.constness, hir::Constness::NotConst)
        || signature.header.abi != rustc_abi::ExternAbi::Rust
    {
        return Err(Failure::Unknown(
            "the native getter declaration is outside its closed schema".into(),
        ));
    }
    let _inline = inline::capture(tcx, owner, work)?;
    let body = raw
        .nodes
        .bodies
        .get(&body_id.hir_id.local_id)
        .copied()
        .ok_or_else(|| Failure::Unknown("the original getter body is absent".into()))?;
    if body.params.len() != 1 || body.contract.is_some() {
        return Err(Failure::Unknown(
            "the original getter has unsupported parameters or contract".into(),
        ));
    }
    let hir::PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) =
        body.params[0].pat.kind
    else {
        return Err(Failure::Unknown(
            "the getter receiver is not a plain native binding".into(),
        ));
    };
    Ok((body, binding))
}

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    nominal: DefId,
    owner: LocalDefId,
    cohort: &Cohort<'_, '_>,
    work: &mut Work,
) -> Result<Helper, Failure> {
    let (body, binding) = body(tcx, owner, work)?;
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return Err(Failure::Unknown(
            "the getter body is not its original block".into(),
        ));
    };
    if !block.stmts.is_empty() {
        return Err(Failure::Unknown(
            "the getter body has unrepresented statements".into(),
        ));
    }
    let expression = block
        .expr
        .ok_or_else(|| Failure::Unknown("the original getter has no tail expression".into()))?;
    let hir::ExprKind::Call(callee, [receiver, variant, field]) = expression.kind else {
        return Err(Failure::Unknown(
            "the original getter is not one field-intrinsic tail call".into(),
        ));
    };
    let hir::ExprKind::Path(ref path) = callee.kind else {
        return Err(Failure::Unknown(
            "the getter's actual callee is not a resolved path".into(),
        ));
    };
    let types = tcx.typeck(owner);
    if !matches!(types.qpath_res(path, callee.hir_id),
        Res::Def(DefKind::Fn, actual) if actual == cohort.intrinsic())
    {
        return Err(Failure::Unknown(
            "the original getter calls another native declaration".into(),
        ));
    }
    let hir::ExprKind::Path(ref receiver_path) = receiver.kind else {
        return Err(Failure::Unknown(
            "the original getter does not read its own receiver".into(),
        ));
    };
    if !matches!(types.qpath_res(receiver_path, receiver.hir_id), Res::Local(id) if id == binding) {
        return Err(Failure::Unknown(
            "the getter receiver belongs to another binding".into(),
        ));
    }
    let ty::Adt(adt, _) = types.expr_ty(receiver).kind() else {
        return Err(Failure::Unknown(
            "the original receiver is not an actual nominal value".into(),
        ));
    };
    if adt.did() != nominal {
        return Err(Failure::Unknown(
            "the original getter receiver has another native nominal type".into(),
        ));
    }
    let (Some(variant), Some(field)) = (literal(variant), literal(field)) else {
        return Err(Failure::Unknown(
            "the original getter does not use literal field metadata".into(),
        ));
    };
    // Pay for the same native inventory the subsequent mode rule inspects.
    work.charge(tcx, adt.variants().len())?;
    for variant in adt.variants() {
        work.charge(tcx, variant.fields.len())?;
    }
    let (variant_index, variant) = adt
        .variants()
        .iter()
        .enumerate()
        .find(|(_, actual)| actual.ident(tcx).name == variant)
        .ok_or_else(|| Failure::Unknown("the getter metadata names no actual variant".into()))?;
    let field_index = variant
        .fields
        .iter()
        .position(|actual| actual.ident(tcx).name == field)
        .ok_or_else(|| Failure::Unknown("the getter metadata names no actual field".into()))?;
    Ok(Helper {
        owner,
        slot: Slot {
            nominal: declaration_native::key(tcx, nominal),
            variant: u32::try_from(variant_index)
                .map_err(|_| Failure::Unknown("variant index overflow".into()))?,
            field: u32::try_from(field_index)
                .map_err(|_| Failure::Unknown("field index overflow".into()))?,
        },
    })
}
