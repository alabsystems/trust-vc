//! Native declaration errors do not license autospec pairs or body reads.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};

use super::super::{
    attrs, declaration_modes, function_identity_observer, is_external, modes, Cx, UserError,
};
use crate::messages::Phase;

fn clean(tcx: TyCtxt<'_>, source: LocalDefId) -> bool {
    tcx.dcx().has_errors().is_none()
        && !is_external(tcx, source)
        && !function_identity_observer::body_is_quarantined(tcx.sess, source)
}

fn same_attributes<'tcx>(
    tcx: TyCtxt<'tcx>,
    source: LocalDefId,
    original: &'tcx hir::OwnerInfo<'tcx>,
) -> bool {
    let root = tcx.local_def_id_to_hir_id(source);
    root.owner.def_id == source
        && std::ptr::eq(tcx.hir_attr_map(root.owner), &original.attrs)
        && std::ptr::eq(tcx.hir_attrs(root), original.attrs.get(root.local_id))
}

/// A40 ignores this metadata on an explicitly external ordinary function.
/// This only preserves the existing External role: it supplies no function
/// registration, logical body, signature modes, or redirection pair.
pub(super) fn external_directive_ignored(cx: &Cx<'_>, source: LocalDefId) -> bool {
    let tcx = cx.tcx;
    if tcx.dcx().has_errors().is_some()
        || !super::ordinary_function(cx, source)
        || function_identity_observer::body_is_quarantined(tcx.sess, source)
    {
        return false;
    }
    let parent = tcx.local_parent(source);
    if !matches!(
        (tcx.def_kind(source), tcx.def_kind(parent)),
        (DefKind::Fn, DefKind::Mod)
            | (DefKind::AssocFn, DefKind::Impl { of_trait: false })
    ) {
        return false;
    }
    let Some(original) = tcx.lower_to_hir(source).as_owner() else {
        return false;
    };
    if !same_attributes(tcx, source, original) {
        return false;
    }
    let attributes = cx.declaration_attrs(source);
    if !attributes.external
        || !attributes.verus_macro
        || attributes.autospec.is_none()
        || !attributes.unsupported.is_empty()
        || attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(source)))
            .iter()
            .any(|(attribute, _)| !matches!(attribute,
                attrs::VerusAttr::External
                    | attrs::VerusAttr::VerusMacro
                    | attrs::VerusAttr::Mode(_)
                    | attrs::VerusAttr::Visibility { .. }
                    | attrs::VerusAttr::WhenUsedAsSpec(_)))
    {
        return false;
    }
    let (declaration, body_id) = match (original.node(), tcx.hir_node_by_def_id(source)) {
        (hir::OwnerNode::Item(raw), hir::Node::Item(now)) if std::ptr::eq(raw, now) => {
            let hir::ItemKind::Fn { sig, body, .. } = &raw.kind else {
                return false;
            };
            (sig.decl, *body)
        }
        (hir::OwnerNode::ImplItem(raw), hir::Node::ImplItem(now)) if std::ptr::eq(raw, now) => {
            let hir::ImplItemKind::Fn(sig, body) = &raw.kind else {
                return false;
            };
            (sig.decl, *body)
        }
        _ => return false,
    };
    let Some(current_declaration) = tcx.hir_fn_decl_by_hir_id(tcx.local_def_id_to_hir_id(source)) else {
        return false;
    };
    let Some(original_body) = original.nodes.bodies.get(&body_id.hir_id.local_id) else {
        return false;
    };
    let Some(body) = tcx.hir_maybe_body_owned_by(source) else {
        return false;
    };
    std::ptr::eq(declaration, current_declaration)
        && std::ptr::eq(body, *original_body)
        && tcx.typeck(source).tainted_by_errors.is_none()
        && same_attributes(tcx, source, original)
        && is_external(tcx, source)
        && tcx.dcx().has_errors().is_none()
        && !function_identity_observer::body_is_quarantined(tcx.sess, source)
}

/// The selected native call still names an ignored ordinary local function.
/// Emit the A40 WF rejection, without manufacturing a mode/body/borrow packet.
pub(super) fn ignored_external_call<'tcx>(
    cx: &Cx<'tcx>,
    caller: LocalDefId,
    body_owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>,
    expression: &'tcx hir::Expr<'tcx>,
    callee: DefId,
) -> Option<UserError> {
    let tcx = cx.tcx;
    let local = callee.as_local()?;
    if caller != body_owner
        || cx.fns.contains_key(&callee)
        || !cx.fns.contains_key(&caller.to_def_id())
        || tcx.dcx().has_errors().is_some()
        || function_identity_observer::body_is_quarantined(tcx.sess, caller)
        || !super::ordinary_function(cx, caller)
        || !declaration_modes::original_body_available(tcx, caller)
        || !std::ptr::eq(typeck, tcx.typeck(caller))
        || typeck.tainted_by_errors.is_some()
        || expression.hir_id.owner.def_id != caller
        || tcx.hir_enclosing_body_owner(expression.hir_id) != caller
        || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        || !external_directive_ignored(cx, local)
    {
        return None;
    }
    let original = tcx.lower_to_hir(caller).as_owner()?;
    if !same_attributes(tcx, caller, original)
        || !clean(tcx, caller)
        || !cx.declaration_attrs(caller).verus_macro
    {
        return None;
    }
    let actual = match expression.kind {
        hir::ExprKind::MethodCall(..) => typeck.type_dependent_def_id(expression.hir_id)?,
        hir::ExprKind::Call(function, _) => {
            let hir::ExprKind::Path(ref path) = function.kind else {
                return None;
            };
            let Res::Def(DefKind::Fn | DefKind::AssocFn, actual) = typeck.qpath_res(path, function.hir_id) else {
                return None;
            };
            actual
        }
        _ => return None,
    };
    if actual != callee
        || !clean(tcx, caller)
        || !same_attributes(tcx, caller, original)
        || !external_directive_ignored(cx, local)
    {
        return None;
    }
    let mut problem = UserError::new(
        Phase::WellFormed,
        expression.span,
        format!(
            "cannot use function `{}` which is ignored because it is either declared outside the verus! macro or it is marked as `external`.",
            tcx.def_path_str(callee),
        ),
    );
    problem.function = Some(caller);
    Some(problem)
}

/// Join the physical original declaration, body and current signature owner.
/// Signature modes are read as data; no completed walk or availability is made.
/// Body-less/split declarations and unknown native contexts retain refusal.
fn signature<'tcx>(cx: &Cx<'tcx>, source: LocalDefId) -> Option<ty::PolyFnSig<'tcx>> {
    let tcx = cx.tcx;
    if !clean(tcx, source) || !super::ordinary_function(cx, source) {
        return None;
    }
    let original = tcx.lower_to_hir(source).as_owner()?;
    // The ordinary provider returns this exact raw AttributeMap. Join its
    // complete inventory and current root slice before interpreting markers
    // or mode attributes; an independent projected attrs provider is unknown.
    if !same_attributes(tcx, source, original) {
        return None;
    }
    let attributes = cx.declaration_attrs(source);
    if !attributes.verus_macro
        || attributes.autospec.is_none()
        || !attributes.unsupported.is_empty()
    {
        return None;
    }
    let current = tcx.hir_node_by_def_id(source);
    let (declaration, body_id) = match (original.node(), current) {
        (hir::OwnerNode::Item(raw), hir::Node::Item(now)) if std::ptr::eq(raw, now) => {
            let hir::ItemKind::Fn { sig, body, .. } = &raw.kind else {
                return None;
            };
            (sig.decl, *body)
        }
        (hir::OwnerNode::ImplItem(raw), hir::Node::ImplItem(now)) if std::ptr::eq(raw, now) => {
            let hir::ImplItemKind::Fn(sig, body) = &raw.kind else {
                return None;
            };
            (sig.decl, *body)
        }
        (hir::OwnerNode::TraitItem(raw), hir::Node::TraitItem(now)) if std::ptr::eq(raw, now) => {
            let hir::TraitItemKind::Fn(sig, hir::TraitFn::Provided(body)) = &raw.kind else {
                return None;
            };
            (sig.decl, *body)
        }
        _ => return None,
    };
    let current_declaration = tcx.hir_fn_decl_by_hir_id(tcx.local_def_id_to_hir_id(source))?;
    let original_body = original.nodes.bodies.get(&body_id.hir_id.local_id).copied()?;
    let body = tcx.hir_maybe_body_owned_by(source)?;
    if !std::ptr::eq(declaration, current_declaration)
        || !std::ptr::eq(body, original_body)
        || declaration.implicit_self() == hir::ImplicitSelfKind::Mut
    {
        return None;
    }
    let native = tcx.fn_sig(source).instantiate_identity().skip_normalization();
    let value = native.skip_binder();
    if value.safety().is_unsafe()
        || value.abi() != super::rustc_abi::ExternAbi::Rust
        || value.c_variadic()
        || value.inputs().len() != declaration.inputs.len()
        || body.params.len() != value.inputs().len()
    {
        return None;
    }
    let parameters = ty::GenericArgs::identity_for_item(tcx, source.to_def_id())
        .types()
        .enumerate()
        .filter_map(|(index, value)| match value.kind() {
            ty::Param(parameter) => u32::try_from(index).ok().map(|index| (parameter.index, index)),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let represented = |value| {
        cx.vc_ty_with(value, &|parameter| parameters.get(&parameter.index).copied())
    };
    if value.inputs().iter().any(|input| represented(*input).is_none())
        || represented(value.output()).is_none()
    {
        return None;
    }
    let modes::SignatureModeResult::Known(modes) =
        modes::signature_modes(cx, source.to_def_id(), tcx.def_span(source))
    else {
        return None;
    };
    if modes.def_id != source.to_def_id()
        || modes.body_owner != source
        || modes.params.len() != body.params.len()
        || !modes.params.iter().zip(body.params).all(|(known, actual)| known.hir_id == actual.hir_id)
        || tcx.typeck(source).tainted_by_errors.is_some()
        || !same_attributes(tcx, source, original)
        || !clean(tcx, source)
    {
        return None;
    }
    Some(native)
}

pub(super) fn mutable_parameter_error(cx: &Cx<'_>, source: LocalDefId) -> Option<UserError> {
    if !cx.opts.new_mut_ref {
        return None;
    }
    let native = signature(cx, source)?;
    if !native.skip_binder().inputs().iter().any(|input| {
        matches!(input.kind(), ty::Ref(_, _, mutability) if mutability.is_mut())
    }) {
        return None;
    }
    // This is the source parameter rule in A40 rust_to_vir_func, before
    // target lookup and before Modes. No target or redirection is admitted.
    let mut error = UserError::new(
        Phase::RustToVir,
        cx.tcx.def_span(source),
        "when_used_as_spec not supported for function with &mut param",
    );
    error.function = Some(source);
    Some(error)
}

pub(super) fn missing_trait_sibling(cx: &Cx<'_>, source: LocalDefId, name: &str) -> bool {
    let tcx = cx.tcx;
    if tcx.def_kind(source) != DefKind::AssocFn || signature(cx, source).is_none() {
        return false;
    }
    let parent = tcx.local_parent(source);
    if tcx.def_kind(parent) != DefKind::Trait
        || tcx.trait_of_assoc(source.to_def_id()) != Some(parent.to_def_id())
        || !clean(tcx, parent)
    {
        return false;
    }
    let inventory = tcx.associated_items(parent);
    let source_present = inventory.in_definition_order().any(|item| {
        item.def_id == source.to_def_id()
            && matches!(item.kind, ty::AssocKind::Fn { .. })
    });
    // The complete native inventory is authoritative for absence. A member
    // of any kind with that spelling stays unsupported rather than being
    // mistaken for a missing function after a filtered registry lookup.
    let any_same_name = inventory.in_definition_order().any(|item| item.name().as_str() == name);
    source_present
        && !any_same_name
        && clean(tcx, source)
        && clean(tcx, parent)
        && signature(cx, source).is_some()
}
