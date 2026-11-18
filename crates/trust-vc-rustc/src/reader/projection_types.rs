//! Native identities for unresolved associated-type constructors.
//!
//! Declarations and closed selected implementations describe type semantics.
//! They supply no solver equation, body, mode, value layout, Copy premise,
//! import or ownership capability.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use rustc_hir::{def::DefKind, def_id::{DefId, LocalDefId}};
use rustc_middle::ty::{self, TyCtxt, TypeckResults, TypeVisitableExt};
use trust_vc_vcir::{ProjectionDecl, ProjectionId, ProjectionImpl, ProjectionValue, Ty};
use std::rc::Rc;

use super::Cx;
mod fields;
pub(super) use fields::observe_fields;

fn current_attributes(tcx: TyCtxt<'_>, source: LocalDefId) -> bool {
    let Some(original) = tcx.lower_to_hir(source).as_owner() else { return false; };
    let root = tcx.local_def_id_to_hir_id(source);
    root.owner.def_id == source
        && std::ptr::eq(tcx.hir_attr_map(root.owner), &original.attrs)
        && std::ptr::eq(tcx.hir_attrs(root), original.attrs.get(root.local_id))
}

pub(super) fn ready(tcx: TyCtxt<'_>, source: LocalDefId) -> bool {
    // Canonical raw attribute maps precede every semantic attribute read,
    // including inherited External classification in associated_types::ready.
    let mut current = Some(source);
    while let Some(owner) = current {
        if !current_attributes(tcx, owner) { return false; }
        current = tcx.opt_local_parent(owner);
    }
    super::associated_types::ready(tcx, source)
}

fn register_member(cx: &Cx<'_>, member: DefId) -> Option<ProjectionId> {
    let tcx = cx.tcx;
    let local = member.as_local()?;
    let parent = tcx.local_parent(local);
    if tcx.def_kind(local) != DefKind::AssocTy || tcx.def_kind(parent) != DefKind::Trait
        || !ready(tcx, local) || !ready(tcx, parent)
        || !super::is_verus_trait(tcx, parent.to_def_id(), cx.opts.no_external_by_default)
        || super::associated_types::trait_problem(tcx, parent).is_some()
        || tcx.generics_of(local).parent != Some(parent.to_def_id())
        || !tcx.generics_of(local).own_params.is_empty()
        || !tcx.associated_items(parent).in_definition_order().any(|item| item.def_id == member)
    { return None; }
    let id = ProjectionId(cx.def_hash(member));
    let declaration = ProjectionDecl {
        id, trait_id: cx.def_hash(parent.to_def_id()),
        arity: tcx.generics_of(parent).count(), name: tcx.def_path_str(member),
        span: cx.span_id(tcx.def_span(member)),
    };
    if !ready(tcx, local) || !ready(tcx, parent) { return None; }
    let mut declarations = cx.projections.borrow_mut();
    if let Some(old) = declarations.get(&member) {
        if old.id != declaration.id || old.trait_id != declaration.trait_id
            || old.arity != declaration.arity || old.name != declaration.name { return None; }
    } else { declarations.insert(member, declaration); }
    Some(id)
}

pub(super) fn current<'tcx>(cx: &Cx<'tcx>, definition: LocalDefId, owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>, checked: &Rc<super::modes::CheckedModes<'tcx>>) -> bool {
    let tcx = cx.tcx;
    tcx.dcx().has_errors().is_none() && typeck.tainted_by_errors.is_none()
        && std::ptr::eq(typeck, tcx.typeck(owner))
        && super::declaration_modes::original_body_available(tcx, owner)
        && super::modes::ModeContext::body_owner(cx, definition) == Some(owner)
        && cx.checked_modes.borrow().get(&definition).is_some_and(|actual| Rc::ptr_eq(actual, checked))
        && checked.bindings.checked(tcx, definition, owner).is_ok()
        && checked.availability.checked(tcx, definition, owner).is_ok()
}

/// Observe actual closed aliases before native instance normalization erases
/// their spelling. Selection, members and RHS are all queried from this same
/// current compiler; syntax and a saved result never define an implementation.
pub(super) fn observe_instance<'tcx>(
    cx: &Cx<'tcx>, definition: LocalDefId, owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>, checked: Option<&Rc<super::modes::CheckedModes<'tcx>>>,
    instantiated: ty::Ty<'tcx>,
) -> Vec<LocalDefId> {
    let Some(checked) = checked else { return Vec::new(); };
    if !current(cx, definition, owner, typeck, checked) { return Vec::new(); }
    let tcx = cx.tcx;
    let environment = ty::TypingEnv::fully_monomorphized();
    let mut used = Vec::new();
    for native in instantiated.walk().filter_map(|argument| argument.as_type()) {
        let ty::Alias(_, alias) = native.kind() else { continue; };
        let ty::AliasTyKind::Projection { def_id: member } = alias.kind else { continue; };
        let collect = || -> Option<(LocalDefId, ProjectionImpl)> {
            if native.has_param() || native.has_infer() || native.has_placeholders()
                || native.has_escaping_bound_vars() || native.references_error()
            { return None; }
            let declaration = member.as_local()?;
            let parent = tcx.local_parent(declaration);
            let _ = register_member(cx, member)?;
            let arguments = tcx.try_normalize_erasing_regions(environment, ty::Unnormalized::new(alias.args)).ok()?;
            let reference = ty::TraitRef::new(tcx, parent.to_def_id(), arguments.iter());
            let Ok(rustc_middle::traits::ImplSource::UserDefined(selection)) =
                tcx.codegen_select_candidate(environment.as_query_input(reference)) else { return None; };
            let implementation = selection.impl_def_id.as_local()?;
            if !ready(tcx, implementation)
                || !super::is_verus_trait_impl(cx, selection.impl_def_id)
                || super::trait_impl_problem(tcx, implementation, cx.opts.no_external_by_default).is_some()
                || super::impl_header_problem(cx, implementation).is_some()
                || !selection.args.is_empty()
            { return None; }
            let selected_reference = tcx.impl_trait_ref(implementation)
                .instantiate(tcx, selection.args).skip_normalization();
            let selected_reference = tcx.try_normalize_erasing_regions(environment,
                ty::Unnormalized::new(selected_reference)).ok()?;
            if selected_reference != reference { return None; }
            let mut represented = Vec::new();
            for argument in arguments.iter() {
                let ty::GenericArgKind::Type(argument) = argument.kind() else { return None; };
                if argument.has_param() || argument.has_infer() || argument.has_placeholders()
                    || argument.has_escaping_bound_vars() || argument.references_error()
                    || cx.mentions_source_opaque(argument)
                    || argument.walk().any(|part| part.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..))))
                { return None; }
                represented.push(cx.vc_ty_with(argument, &|_| None)?);
            }
            let normalized = tcx.try_normalize_erasing_regions(environment, ty::Unnormalized::new(native)).ok()?;
            let mut values = Vec::new();
            let mut matched = false;
            for item in tcx.associated_items(implementation).in_definition_order() {
                let source = item.def_id.as_local()?;
                let original = item.trait_item_def_id()?;
                if !matches!(item.kind, ty::AssocKind::Type { .. })
                    || tcx.local_parent(source) != implementation
                    || tcx.parent(original) != parent.to_def_id()
                    || !ready(tcx, source) || !ready(tcx, original.as_local()?)
                { return None; }
                let identity = register_member(cx, original)?;
                let rhs = tcx.try_normalize_erasing_regions(environment,
                    tcx.type_of(source).instantiate(tcx, selection.args)).ok()?;
                if rhs.has_param() || rhs.has_infer() || rhs.has_placeholders()
                    || rhs.has_escaping_bound_vars() || rhs.references_error()
                    || cx.mentions_source_opaque(rhs)
                    || rhs.walk().any(|argument| argument.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..))))
                { return None; }
                if original == member {
                    if rhs != normalized || matched { return None; }
                    matched = true;
                }
                values.push(ProjectionValue { declaration: identity,
                    definition: cx.def_hash(item.def_id), ty: cx.vc_ty_with(rhs, &|_| None)? });
            }
            if !matched || !ready(tcx, declaration) || !ready(tcx, parent)
                || !ready(tcx, implementation) || !current(cx, definition, owner, typeck, checked)
            { return None; }
            Some((implementation, ProjectionImpl { id: cx.def_hash(selection.impl_def_id),
                trait_id: cx.def_hash(parent.to_def_id()), arguments: represented,
                values, span: cx.span_id(tcx.def_span(implementation)) }))
        };
        if let Some((implementation, value)) = collect() {
            let mut definitions = cx.projection_impls.borrow_mut();
            if let Some(previous) = definitions.get(&implementation.to_def_id()) {
                if previous.id != value.id || previous.trait_id != value.trait_id
                    || previous.arguments != value.arguments || previous.values != value.values
                { continue; }
            } else { definitions.insert(implementation.to_def_id(), value); }
            if !used.contains(&implementation) { used.push(implementation); }
        }
    }
    used
}

pub(super) fn lower<'tcx>(
    cx: &Cx<'tcx>,
    native: ty::Ty<'tcx>,
    param: &dyn Fn(ty::ParamTy) -> Option<u32>,
) -> Option<Ty> {
    let tcx = cx.tcx;
    if tcx.dcx().has_errors().is_some() { return None; }
    let ty::Alias(_, alias) = native.kind() else { return None; };
    let ty::AliasTyKind::Projection { def_id } = alias.kind else { return None; };
    let member = def_id.as_local()?;
    if tcx.def_kind(member) != DefKind::AssocTy || !ready(tcx, member) { return None; }
    let trait_owner = tcx.local_parent(member);
    if tcx.def_kind(trait_owner) != DefKind::Trait || !ready(tcx, trait_owner)
        || !super::is_verus_trait(tcx, trait_owner.to_def_id(), cx.opts.no_external_by_default)
        || super::associated_types::trait_problem(tcx, trait_owner).is_some()
    {
        return None;
    }
    // The source admission slice still requires a plain local trait with
    // Self only, no GATs/defaults/foreign or unrepresented associated items.
    // Never discard an argument or infer a declaration from its spelling.
    let generics = tcx.generics_of(member);
    if generics.parent != Some(trait_owner.to_def_id()) || !generics.own_params.is_empty()
        || alias.args.len() != tcx.generics_of(trait_owner).count()
    {
        return None;
    }
    let item = tcx.associated_item(def_id);
    if !matches!(item.kind, ty::AssocKind::Type { .. })
        || !tcx.associated_items(trait_owner).in_definition_order().any(|i| i.def_id == def_id)
    {
        return None;
    }
    let mut arguments = Vec::new();
    for argument in alias.args.iter() {
        let ty::GenericArgKind::Type(value) = argument.kind() else { return None; };
        if cx.mentions_source_opaque(value) { return None; }
        arguments.push(cx.vc_ty_with(value, param)?);
    }
    let id = ProjectionId(cx.def_hash(def_id));
    let trait_id = cx.def_hash(trait_owner.to_def_id());
    let name = tcx.def_path_str(def_id);
    let span = tcx.def_span(member);
    if !ready(tcx, member) || !ready(tcx, trait_owner) || tcx.dcx().has_errors().is_some() {
        return None;
    }
    let mut declarations = cx.projections.borrow_mut();
    match declarations.get(&def_id) {
        Some(old) if old.id != id || old.trait_id != trait_id
            || old.arity != arguments.len() || old.name != name => return None,
        Some(_) => {}
        None => {
            declarations.insert(def_id, ProjectionDecl {
                id, trait_id, arity: arguments.len(), name, span: cx.span_id(span),
            });
        }
    }
    Some(Ty::Projection(id, arguments))
}
