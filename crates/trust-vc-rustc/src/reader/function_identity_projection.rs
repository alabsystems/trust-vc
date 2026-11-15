//! Coherent observation-only projection of a checked identity helper.
//!
//! This function installs no query provider. A future unverified adapter may
//! use it; proof-active use requires the permanent in-tree Trust engine hook.
//! The original graph stays available for provenance/header inspection, and
//! ordinary function bodies and native MIR ownership gates are untouched.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::hir::{ProjectedMaybeOwner, ProjectedOwnerInfo};
use rustc_middle::ty::TyCtxt;

use super::function_identity::{ParsedHelper, Problem, Target};

pub(super) struct ObservationProjection<'tcx> {
    pub(super) projected: ProjectedMaybeOwner<'tcx>,
    pub(super) original: &'tcx hir::OwnerInfo<'tcx>,
}

pub(super) fn unit_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: &'tcx hir::OwnerInfo<'tcx>,
    helper: &ParsedHelper<'tcx>,
) -> Result<ObservationProjection<'tcx>, Problem> {
    let problem = |detail| Problem {
        at: helper.original_body.value.span,
        detail,
    };
    // Associated syntax does not identify a concrete implementation merely
    // because its printed name matches an item. Keep it unresolved until the
    // native identity resolver establishes the exact declaration relation.
    let Target::Declaration(target) = helper.target else {
        return Err(problem(
            "an associated identity requires native resolution before projection",
        ));
    };
    if tcx.def_kind(target) != rustc_hir::def::DefKind::Fn {
        return Err(problem(
            "this first observation projection supports free function declarations only",
        ));
    }
    let OwnerNode::Item(old_item) = original.node() else {
        return Err(problem(
            "the original identity helper is not a function item",
        ));
    };
    let hir::ItemKind::Fn {
        body: old_body_id, ..
    } = old_item.kind
    else {
        return Err(problem(
            "the original identity helper is not a function item",
        ));
    };
    if original
        .nodes
        .bodies
        .get(&old_body_id.hir_id.local_id)
        .is_none_or(|body| !std::ptr::eq(*body, helper.original_body))
    {
        return Err(problem(
            "the helper record belongs to another original graph",
        ));
    }
    if !tcx
        .visibility(target)
        .is_accessible_from(old_item.owner_id.def_id.to_def_id(), tcx)
    {
        return Err(problem(
            "the original function-identity target is not visible from this module",
        ));
    }
    project(tcx, original, helper)
}

/// Pending targets may be observed only in the explicit unverified adapter.
/// Their identity/visibility remains Pending until post-analysis native lookup;
/// failure there cannot become header, import, reveal or proof authority.
pub(super) fn unverified_observation_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: &'tcx hir::OwnerInfo<'tcx>,
    helper: &ParsedHelper<'tcx>,
) -> Result<ObservationProjection<'tcx>, Problem> {
    if tcx.sess.trust_verification_enabled()
        || tcx.sess.trust_ir_lower_enabled()
        || tcx.sess.opts.unstable_opts.trust_targo_test_monitor
        || tcx.sess.opts.unstable_opts.trust_certified_test_monitors
    {
        return Err(Problem { at: helper.original_body.value.span,
            detail: "the observation projection is unavailable to verification, direct IR or test monitors" });
    }
    project(tcx, original, helper)
}

fn project<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: &'tcx hir::OwnerInfo<'tcx>,
    helper: &ParsedHelper<'tcx>,
) -> Result<ObservationProjection<'tcx>, Problem> {
    let problem = |detail| Problem {
        at: helper.original_body.value.span,
        detail,
    };
    let OwnerNode::Item(old_item) = original.node() else {
        return Err(problem(
            "the original identity helper is not a function item",
        ));
    };
    let hir::ItemKind::Fn {
        body: old_body_id, ..
    } = old_item.kind
    else {
        return Err(problem(
            "the original identity helper is not a function item",
        ));
    };
    if original
        .nodes
        .bodies
        .get(&old_body_id.hir_id.local_id)
        .is_none_or(|body| !std::ptr::eq(*body, helper.original_body))
    {
        return Err(problem(
            "the helper record belongs to another original graph",
        ));
    }
    // There is no lint-id remapping policy in this small projection. A real
    // delayed diagnostic must not be dropped or attached to a different node.
    if !original.delayed_lints.borrow().is_empty() {
        return Err(problem(
            "delayed diagnostics require a checked identity projection map",
        ));
    }
    let Some(value_id) = original.nodes.nodes.indices().nth(1) else {
        return Err(problem("the original identity helper has no body node"));
    };
    let value_hir_id = hir::HirId {
        owner: old_item.owner_id,
        local_id: value_id,
    };
    let value = tcx.hir_arena.alloc(hir::Expr {
        hir_id: value_hir_id,
        kind: hir::ExprKind::Tup(&[]),
        span: helper.original_body.value.span,
    });
    let body = tcx.hir_arena.alloc(hir::Body {
        params: &[],
        value,
        contract: None,
    });
    let mut item = *old_item;
    let hir::ItemKind::Fn { body: body_id, .. } = &mut item.kind else {
        return Err(problem("the copied identity helper is not a function item"));
    };
    *body_id = body.id();
    let item = tcx.hir_arena.alloc(item);
    let mut bodies = original.nodes.bodies.clone();
    bodies.clear();
    bodies.insert(value_id, body);
    let hashes = tcx.hash_owner_nodes(
        OwnerNode::Item(item),
        &bodies,
        &original.attrs.map,
        original.attrs.define_opaque,
    );
    if hashes.attrs_hash != original.attrs.opt_hash {
        return Err(problem(
            "the identity projection changed the original attribute hash",
        ));
    }
    // Item0 and Unit1 form a dense owner; keeping the former high-ID root
    // while deleting its children violates rustc's HIR-ID validator. The
    // parser has already excluded retained parameter/type/contract/generic
    // nodes and nested owners. Update both the body map and the node index.
    let mut nodes = original.nodes.nodes.clone();
    nodes.truncate(2);
    nodes[hir::ItemLocalId::ZERO] = hir::ParentedNode {
        parent: hir::ItemLocalId::INVALID,
        node: hir::Node::Item(item),
    };
    nodes[value_id] = hir::ParentedNode {
        parent: hir::ItemLocalId::ZERO,
        node: hir::Node::Expr(value),
    };
    let nodes = tcx.arena.alloc(hir::OwnerNodes {
        opt_hash: hashes.bodies_hash,
        nodes,
        bodies,
    });
    let mut traits = original.trait_map.clone();
    traits.clear();
    let traits = tcx.arena.alloc(traits);
    Ok(ObservationProjection {
        projected: ProjectedMaybeOwner::Owner(ProjectedOwnerInfo::new(
            nodes,
            &original.parenting,
            traits,
            &original.delayed_lints,
        )),
        original,
    })
}
