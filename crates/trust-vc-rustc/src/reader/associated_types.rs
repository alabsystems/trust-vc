//! Plain native associated-type declarations and closed scalar assignments.
//!
//! These identities enter the ordinary trait dependency graph. No projection
//! type, equation or replacement value is created. Ground value types must
//! already have been normalized by the actual compiler.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use rustc_hir::{self as hir, def::DefKind, def_id::LocalDefId, OwnerNode};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};

use super::{attrs, Refusal};

fn problem(tcx: TyCtxt<'_>, owner: LocalDefId, detail: &str) -> Option<Refusal> {
    Some(Refusal::new("associated-type", detail, tcx.def_span(owner)))
}

/// Queries must still refer to the original, available local declaration.
/// Check the adapter's quarantine only after the ordinary native queries.
pub(super) fn ready(tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
    if tcx.dcx().has_errors().is_some() || super::is_external(tcx, owner) {
        return false;
    }
    let Some(original) = tcx.lower_to_hir(owner).as_owner() else {
        return false;
    };
    let same = match (original.node(), tcx.hir_node_by_def_id(owner)) {
        (OwnerNode::Item(a), hir::Node::Item(b)) => std::ptr::eq(a, b),
        (OwnerNode::TraitItem(a), hir::Node::TraitItem(b)) => std::ptr::eq(a, b),
        (OwnerNode::ImplItem(a), hir::Node::ImplItem(b)) => std::ptr::eq(a, b),
        _ => false,
    };
    let mut current = Some(owner);
    while let Some(local) = current {
        if super::function_identity_observer::body_is_quarantined(tcx.sess, local) {
            return false;
        }
        current = tcx.opt_local_parent(local);
    }
    same && tcx.dcx().has_errors().is_none()
}

fn plain_attributes(tcx: TyCtxt<'_>, owner: LocalDefId) -> Option<Refusal> {
    for (attribute, span) in attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner))) {
        if !matches!(attribute, attrs::VerusAttr::VerusMacro) {
            return Some(Refusal::new(
                "associated-type-attribute",
                format!("{attribute:?} on a plain associated-type declaration or assignment"),
                span,
            ));
        }
    }
    None
}

/// Additional to the ordinary unsafe, source, generic and bound gates.
/// Method-only traits keep their old path. This fragment has no methods,
/// constants, GATs, defaults or user associated/supertrait bounds.
pub(super) fn trait_problem(tcx: TyCtxt<'_>, owner: LocalDefId) -> Option<Refusal> {
    let items = tcx.associated_items(owner);
    if !items
        .in_definition_order()
        .any(|item| matches!(item.kind, ty::AssocKind::Type { .. }))
    {
        return None;
    }
    if !ready(tcx, owner) {
        return problem(
            tcx,
            owner,
            "no error-free original local associated-type trait is available",
        );
    }
    if let Some(problem) = plain_attributes(tcx, owner) {
        return Some(problem);
    }
    let generics = tcx.generics_of(owner);
    if !generics.has_self || generics.own_params.len() != 1 {
        return problem(
            tcx,
            owner,
            "a plain associated-type trait with extra parameters",
        );
    }
    for (clause, _) in tcx
        .explicit_super_clauses_of(owner)
        .skip_binder()
        .iter()
        .chain(tcx.explicit_clauses_of(owner).clauses.iter())
    {
        let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() else {
            return problem(tcx, owner, "a bound on a plain associated-type trait");
        };
        if predicate.polarity != ty::ClausePolarity::Positive
            || !matches!(predicate.self_ty().kind(), ty::Param(parameter) if parameter.index == 0)
            || !(predicate.def_id() == owner.to_def_id()
                || super::is_sizedness_trait(tcx, predicate.def_id()))
        {
            return problem(tcx, owner, "a user bound on a plain associated-type trait");
        }
    }
    for item in items.in_definition_order() {
        let Some(local) = item.def_id.as_local() else {
            return problem(
                tcx,
                owner,
                "a nonlocal associated declaration in a local trait",
            );
        };
        if !matches!(item.kind, ty::AssocKind::Type { .. }) || tcx.local_parent(local) != owner {
            return problem(
                tcx,
                owner,
                "a trait mixing associated types with methods or constants",
            );
        }
        if !ready(tcx, local) {
            return problem(
                tcx,
                local,
                "no original associated declaration is available",
            );
        }
        if let Some(problem) = plain_attributes(tcx, local) {
            return Some(problem);
        }
        if !tcx.generics_of(local).own_params.is_empty()
            || !tcx.explicit_clauses_of(local).clauses.is_empty()
        {
            return problem(tcx, local, "a generic or constrained associated type");
        }
        let hir::Node::TraitItem(declaration) = tcx.hir_node_by_def_id(local) else {
            return problem(
                tcx,
                local,
                "an associated declaration without its original trait item",
            );
        };
        if !matches!(declaration.kind, hir::TraitItemKind::Type(bounds, None) if bounds.is_empty())
        {
            return problem(
                tcx,
                local,
                "an associated type with a default or explicit bounds",
            );
        }
        if !ready(tcx, local) {
            return problem(tcx, local, "the associated declaration became unavailable");
        }
    }
    if !ready(tcx, owner) {
        return problem(tcx, owner, "the associated-type trait became unavailable");
    }
    None
}

/// Ordinary impl header checks still follow this finite member check. Rustc
/// supplies the real assignment type and declaration join; source syntax is
/// never interpreted as a type-equality theorem.
pub(super) fn impl_problem(tcx: TyCtxt<'_>, owner: LocalDefId, loose: bool) -> Option<Refusal> {
    let items = tcx.associated_items(owner);
    if !items
        .in_definition_order()
        .any(|item| matches!(item.kind, ty::AssocKind::Type { .. }))
    {
        return None;
    }
    if !ready(tcx, owner) {
        return problem(
            tcx,
            owner,
            "no error-free original local associated-type implementation is available",
        );
    }
    if let Some(problem) = plain_attributes(tcx, owner) {
        return Some(problem);
    }
    if !tcx.generics_of(owner).own_params.is_empty()
        || !tcx.explicit_clauses_of(owner).clauses.is_empty()
    {
        return problem(
            tcx,
            owner,
            "a generic or constrained associated-type implementation",
        );
    }
    let reference = tcx
        .impl_trait_ref(owner)
        .instantiate_identity()
        .skip_normalization();
    let Some(declaration) = reference.def_id.as_local() else {
        return problem(tcx, owner, "an associated assignment of a foreign trait");
    };
    if !super::is_verus_trait(tcx, reference.def_id, loose) {
        return problem(
            tcx,
            owner,
            "an associated assignment without its selected local trait",
        );
    }
    if let Some(problem) = trait_problem(tcx, declaration) {
        return Some(problem);
    }
    if reference.has_param()
        || reference.has_infer()
        || reference.has_placeholders()
        || reference.has_escaping_bound_vars()
        || reference.references_error()
    {
        return problem(
            tcx,
            owner,
            "an open associated-type implementation identity",
        );
    }
    for item in items.in_definition_order() {
        let Some(local) = item.def_id.as_local() else {
            return problem(
                tcx,
                owner,
                "a nonlocal associated assignment in a local implementation",
            );
        };
        let Some(original) = item.trait_item_def_id() else {
            return problem(
                tcx,
                local,
                "an associated assignment without its native declaration",
            );
        };
        if !matches!(item.kind, ty::AssocKind::Type { .. })
            || tcx.local_parent(local) != owner
            || tcx.parent(original) != reference.def_id
            || tcx.def_kind(original) != DefKind::AssocTy
        {
            return problem(
                tcx,
                local,
                "an associated assignment with a different native owner or member",
            );
        }
        let Some(original) = original.as_local() else {
            return problem(tcx, local, "a nonlocal associated declaration");
        };
        if !ready(tcx, local) || !ready(tcx, original) {
            return problem(
                tcx,
                local,
                "no original assignment and declaration are available",
            );
        }
        if let Some(problem) = plain_attributes(tcx, local) {
            return Some(problem);
        }
        if !tcx.generics_of(local).own_params.is_empty()
            || !tcx.explicit_clauses_of(local).clauses.is_empty()
        {
            return problem(tcx, local, "a generic or constrained associated assignment");
        }
        if !matches!(tcx.hir_node_by_def_id(local), hir::Node::ImplItem(assignment) if matches!(assignment.kind, hir::ImplItemKind::Type(_)))
        {
            return problem(
                tcx,
                local,
                "an associated assignment without its original type item",
            );
        }
        let native = tcx
            .type_of(local)
            .instantiate_identity()
            .skip_normalization();
        if !matches!(native.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
            && !matches!(native.kind(), ty::Tuple(fields) if fields.is_empty())
        {
            return problem(
                tcx,
                local,
                "an associated assignment outside the closed scalar/unit fragment",
            );
        }
        if !ready(tcx, local) || !ready(tcx, original) {
            return problem(
                tcx,
                local,
                "the assignment or declaration became unavailable",
            );
        }
    }
    if !ready(tcx, owner) || !ready(tcx, declaration) {
        return problem(tcx, owner, "the implementation or trait became unavailable");
    }
    None
}
