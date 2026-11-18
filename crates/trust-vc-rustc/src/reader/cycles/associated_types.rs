//! Preserve declaration dependencies before ground field normalization.
//!
//! A40 `recursive_types.rs::build_datatype_graph` visits datatype bounds and
//! fields, and associated assignments' Self/arguments/RHS. Each native datatype
//! occurrence also carries the implementations its bounds need, selected in
//! the original occurrence's environment (`rust_to_vir_base::get_impl_paths`).
//! Only a cycle through an associated implementation is an error here. The
//! ordinary datatype base-case and function/call graphs keep their own checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{self as mty, TyCtxt, TypeVisitable, TypeVisitableExt, TypeVisitor};
use trust_vc_vcir::{AdtDecl, Ty, VcCrate};

use super::{super::associated_types, Cx, Item, Refusal, UserError};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Node {
    Datatype(Item),
    Impl(Item),
}

struct Build<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    datatypes: BTreeSet<Item>,
    implementations: BTreeSet<Item>,
    edges: BTreeMap<Node, BTreeSet<Node>>,
    pending: BTreeSet<Node>,
    work: &'a mut usize,
}

fn charge(work: &mut usize, amount: usize, tcx: TyCtxt<'_>, origin: DefId) -> Result<(), Refusal> {
    match work.checked_sub(amount) {
        Some(left) => {
            *work = left;
            Ok(())
        }
        None => {
            *work = 0;
            Err(problem(
                tcx,
                origin,
                "the existing trait-dependency traversal grant was exhausted",
            ))
        }
    }
}

fn problem(tcx: TyCtxt<'_>, origin: DefId, detail: &str) -> Refusal {
    Refusal::new("associated-type-dependency", detail, tcx.def_span(origin))
}

/// Inspect the actual occurrence predicates on the same graph ledger.
/// No cloned clause list, synthetic bound, saved match or new allowance.
fn parameter_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: mty::TypingEnv<'tcx>,
    reference: mty::TraitRef<'tcx>,
    origin: DefId,
    work: &mut usize,
) -> Result<bool, Refusal> {
    charge(work, 1, tcx, origin)?;
    let mut clauses = env.param_env.caller_bounds();
    loop {
        charge(work, 1, tcx, origin)?;
        let Some(clause) = clauses.next() else {
            return Ok(false);
        };
        let mty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() else {
            continue;
        };
        if predicate.polarity == mty::ClausePolarity::Positive
            && tcx.erase_and_anonymize_regions(predicate.trait_ref)
                == tcx.erase_and_anonymize_regions(reference)
        {
            return Ok(true);
        }
    }
}

/// Match A40's actual occurrence environment, including its caller bounds.
/// A failed native query is never interpreted as absence of a dependency.
fn implementations<'tcx>(
    tcx: TyCtxt<'tcx>,
    datatype: DefId,
    args: mty::GenericArgs<'tcx>,
    origin: DefId,
    remaining: &mut usize,
) -> Result<Vec<LocalDefId>, Refusal> {
    let env = mty::TypingEnv::non_body_analysis(tcx, origin);
    let clauses = tcx.clauses_of(datatype).instantiate(tcx, args).clauses;
    charge(remaining, clauses.len(), tcx, origin)?;
    let mut work: Vec<_> = clauses
        .into_iter()
        .map(|clause| clause.skip_normalization())
        .collect();
    let mut selected = Vec::new();
    let mut index = 0;
    while index < work.len() && index < super::MAX_BOUND_DEPENDENCIES {
        charge(remaining, 1, tcx, origin)?;
        let clause = work[index];
        index += 1;
        let mty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() else {
            continue;
        };
        let reference = tcx.erase_and_anonymize_regions(predicate.trait_ref);
        if reference.has_escaping_bound_vars() {
            return Err(problem(
                tcx,
                origin,
                "a native type dependency has an escaping binder",
            ));
        }
        let candidate = tcx.codegen_select_candidate(env.as_query_input(reference));
        let candidate = match candidate {
            Ok(value) => value,
            Err(_) => {
                let normalized = super::normalized_trait_ref(tcx, env, reference, origin)?;
                tcx.codegen_select_candidate(env.as_query_input(normalized))
                    .map_err(|_| {
                        problem(
                            tcx,
                            origin,
                            "the original environment cannot select a native type dependency",
                        )
                    })?
            }
        };
        if let rustc_middle::traits::ImplSource::UserDefined(data) = candidate {
            if let Some(local) = data.impl_def_id.as_local() {
                if !selected.contains(&local) {
                    charge(remaining, selected.len() + 1, tcx, origin)?;
                    selected.push(local);
                }
            }
            for nested in tcx
                .clauses_of(data.impl_def_id)
                .instantiate(tcx, data.args)
                .clauses
            {
                let nested = nested.skip_normalization();
                charge(remaining, work.len() + 1, tcx, origin)?;
                if !work.contains(&nested) {
                    work.push(nested);
                }
            }
        }
    }
    if index < work.len() {
        return Err(problem(
            tcx,
            origin,
            "the existing trait-dependency traversal grant was exhausted",
        ));
    }
    if tcx.dcx().has_errors().is_some() {
        return Err(problem(
            tcx,
            origin,
            "native diagnostics reject the type dependencies",
        ));
    }
    Ok(selected)
}

struct Types<'a, 'tcx> {
    roots: Vec<mty::Ty<'tcx>>,
    work: &'a mut usize,
    failed: bool,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for Types<'_, 'tcx> {
    fn visit_ty(&mut self, ty: mty::Ty<'tcx>) {
        // Collect roots only. Native Ty::walk below visits their arguments
        // iteratively, debiting the same graph ledger before each operation.
        if let Some(left) = self.work.checked_sub(1) {
            *self.work = left;
            self.roots.push(ty);
        } else {
            *self.work = 0;
            self.failed = true;
        }
    }
}

impl<'tcx> Build<'_, 'tcx> {
    fn native<T: TypeVisitable<TyCtxt<'tcx>>>(
        &mut self,
        from: Node,
        value: T,
        origin: DefId,
    ) -> Result<(), Refusal> {
        let tcx = self.cx.tcx;
        let roots = {
            let mut types = Types {
                roots: Vec::new(),
                work: &mut *self.work,
                failed: false,
            };
            value.visit_with(&mut types);
            if types.failed {
                return Err(problem(
                    tcx,
                    origin,
                    "the existing trait-dependency traversal grant was exhausted",
                ));
            }
            types.roots
        };
        for native in roots
            .into_iter()
            .flat_map(|root| root.walk().filter_map(|argument| argument.as_type()))
        {
            charge(self.work, 1, tcx, origin)?;
            if let mty::Alias(_, alias) = native.kind() {
                if let mty::AliasTyKind::Projection { def_id: member } = alias.kind {
                    let Some(local) = member.as_local() else {
                        return Err(problem(
                            tcx,
                            origin,
                            "a projected field has no source-owned associated declaration",
                        ));
                    };
                    let parent = tcx.local_parent(local);
                    if tcx.def_kind(local) != DefKind::AssocTy
                        || tcx.def_kind(parent) != DefKind::Trait
                        || !super::super::projection_types::ready(tcx, local)
                        || !super::super::projection_types::ready(tcx, parent)
                        || associated_types::trait_problem(tcx, parent).is_some()
                        || !super::super::is_verus_trait(
                            tcx,
                            parent.to_def_id(),
                            self.cx.opts.no_external_by_default,
                        )
                        || tcx.generics_of(parent).count() != alias.args.len()
                        || !tcx
                            .associated_items(parent)
                            .in_definition_order()
                            .any(|item| item.def_id == member)
                    {
                        return Err(problem(
                            tcx,
                            origin,
                            "a projected field lost its original trait/member/argument identity",
                        ));
                    }
                    let env = mty::TypingEnv::non_body_analysis(tcx, origin);
                    let reference = mty::TraitRef::new(tcx, parent.to_def_id(), alias.args.iter());
                    let selected = tcx.codegen_select_candidate(env.as_query_input(reference))
                        .map_err(|_| problem(tcx, origin, "the original occurrence environment cannot select its associated dependency"))?;
                    match selected {
                        rustc_middle::traits::ImplSource::UserDefined(selected) => {
                            let Some(implementation) = selected.impl_def_id.as_local() else { return Err(problem(tcx, origin, "a projected field selected an unowned foreign implementation")); };
                            if !self.implementations.contains(&Item(implementation))
                                || !super::super::projection_types::ready(tcx, implementation)
                            { return Err(problem(tcx, origin, "a projected field selected an unavailable implementation")); }
                            let selected_reference = tcx.impl_trait_ref(implementation)
                                .instantiate(tcx, selected.args).skip_normalization();
                            if super::normalized_trait_ref(tcx, env, selected_reference, origin)?
                                != super::normalized_trait_ref(tcx, env, reference, origin)? {
                                return Err(problem(tcx, origin, "the selected associated implementation has different complete occurrence arguments"));
                            }
                            let mut matching = tcx.associated_items(implementation).in_definition_order()
                                .filter(|item| item.trait_item_def_id() == Some(member));
                            let Some(definition) = matching.next() else { return Err(problem(tcx, origin, "the selected implementation has no associated member definition")); };
                            let Some(definition_owner) = definition.def_id.as_local() else { return Err(problem(tcx, origin, "the selected associated definition is not source-owned")); };
                            if matching.next().is_some()
                                || !matches!(definition.kind, mty::AssocKind::Type { .. })
                                || tcx.local_parent(definition_owner) != implementation
                                || !super::super::projection_types::ready(tcx, definition_owner)
                            { return Err(problem(tcx, origin, "the selected associated definition has an ambiguous or unavailable owner")); }
                            let rhs = tcx.try_normalize_erasing_regions(env,
                                tcx.type_of(definition.def_id).instantiate(tcx, selected.args))
                                .map_err(|_| problem(tcx, origin, "the selected associated RHS cannot be normalized in its occurrence environment"))?;
                            let actual = tcx.try_normalize_erasing_regions(env, mty::Unnormalized::new(native))
                                .map_err(|_| problem(tcx, origin, "the actual projection cannot be normalized in its occurrence environment"))?;
                            if rhs != actual || rhs.references_error()
                                || !super::super::projection_types::ready(tcx, definition_owner)
                            { return Err(problem(tcx, origin, "the selected associated definition and actual normalized projection disagree")); }
                            charge(self.work, 2, tcx, origin)?;
                            let target = Node::Impl(Item(implementation));
                            self.edges.entry(from).or_default().insert(target);
                            self.pending.insert(target);
                        }
                        rustc_middle::traits::ImplSource::Param(_) if parameter_bound(tcx, env, reference, origin, self.work)? => {
                            // This is an actual occurrence predicate, not a
                            // fabricated concrete selection. All represented
                            // associated implementations are still independent
                            // graph roots; their raw Self/RHS obligations can
                            // expose a Self:T cycle hidden by this caller env.
                        }
                        _ => return Err(problem(tcx, origin, "an associated dependency has no represented native implementation or abstract parameter bound")),
                    }
                    if !super::super::projection_types::ready(tcx, local)
                        || !super::super::projection_types::ready(tcx, parent)
                    {
                        return Err(problem(
                            tcx,
                            origin,
                            "the associated dependency became unavailable",
                        ));
                    }
                }
            }
            let mty::Adt(datatype, args) = native.kind() else {
                continue;
            };
            // Native foreign decorations supply no local field authority.
            let Some(local) = datatype.did().as_local() else {
                continue;
            };
            if !self.datatypes.contains(&Item(local))
                || !super::super::projection_types::ready(tcx, local)
            {
                return Err(problem(
                    tcx,
                    origin,
                    "a required original local datatype is unavailable",
                ));
            }
            let target = Node::Datatype(Item(local));
            charge(self.work, 2, tcx, origin)?;
            self.edges.entry(from).or_default().insert(target);
            self.pending.insert(target);
            for implementation in implementations(tcx, datatype.did(), *args, origin, self.work)? {
                if self.implementations.contains(&Item(implementation)) {
                    charge(self.work, 1, tcx, origin)?;
                    self.edges
                        .entry(from)
                        .or_default()
                        .insert(Node::Impl(Item(implementation)));
                }
            }
        }
        Ok(())
    }
}

pub(super) fn find(
    cx: &Cx<'_>,
    krate: &VcCrate,
    items: &[LocalDefId],
) -> Result<Option<UserError>, Refusal> {
    let adts = cx
        .adts
        .iter()
        .filter_map(|(native, id)| {
            let local = native.as_local()?;
            krate
                .adts
                .iter()
                .find(|decl| decl.id == *id)
                .map(|decl| (local, decl))
        })
        .collect::<Vec<_>>();
    find_with_adts(cx, &adts, items)
}

pub(super) fn find_with_adts(
    cx: &Cx<'_>,
    adts: &[(LocalDefId, &AdtDecl)],
    items: &[LocalDefId],
) -> Result<Option<UserError>, Refusal> {
    let mut work = super::MAX_BOUND_DEPENDENCIES;
    find_with_work(cx, adts, items, &mut work)
}

pub(super) fn find_with_work(
    cx: &Cx<'_>,
    adts: &[(LocalDefId, &AdtDecl)],
    items: &[LocalDefId],
    work: &mut usize,
) -> Result<Option<UserError>, Refusal> {
    let tcx = cx.tcx;
    let origin = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
    let associated_impl = |owner: &LocalDefId| {
        matches!(tcx.def_kind(*owner), DefKind::Impl { of_trait: true })
            && tcx
                .associated_items(*owner)
                .in_definition_order()
                .any(|member| matches!(member.kind, mty::AssocKind::Type { .. }))
    };
    fn projected(ty: &Ty) -> bool {
        match ty {
            Ty::Projection(..) => true,
            Ty::Adt(_, args) | Ty::Tuple(args) => args.iter().any(projected),
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => projected(inner),
            _ => false,
        }
    }
    // A rejection-only structural preflight leaves the old unrelated datatype
    // path unchanged. No projection can take its permissive base-case branch
    // when this exact borrowed field inventory contains none.
    let projected_datatypes = adts.iter().filter(|(_, declaration)| {
        declaration
            .variants
            .iter()
            .any(|variant| variant.fields.iter().any(|field| projected(&field.ty)))
    });
    if !items.iter().any(associated_impl) && projected_datatypes.clone().next().is_none() {
        return Ok(None);
    }
    charge(work, items.len() + adts.len(), tcx, origin)?;
    let implementations: BTreeSet<_> = items
        .iter()
        .copied()
        .filter(associated_impl)
        .map(Item)
        .collect();
    // Only the new associated-implementation reachability closure is visited.
    // An unrelated represented datatype does not acquire new admission gates.
    let mut datatypes = BTreeSet::new();
    let mut pending = BTreeSet::new();
    for (owner, declaration) in adts {
        if cx.adt_id(owner.to_def_id()) != Some(declaration.id) || !datatypes.insert(Item(*owner)) {
            return Err(problem(
                tcx,
                owner.to_def_id(),
                "the datatype graph has no unique current source declaration",
            ));
        }
        if declaration
            .variants
            .iter()
            .any(|variant| variant.fields.iter().any(|field| projected(&field.ty)))
        {
            charge(work, 1, tcx, owner.to_def_id())?;
            pending.insert(Node::Datatype(Item(*owner)));
        }
    }
    charge(work, implementations.len(), tcx, origin)?;
    pending.extend(implementations.iter().copied().map(Node::Impl));
    let mut build = Build {
        cx,
        datatypes,
        pending,
        implementations,
        edges: BTreeMap::new(),
        work,
    };
    let mut seen = BTreeSet::new();
    while let Some(node) = build.pending.pop_first() {
        charge(build.work, 1, tcx, origin)?;
        if !seen.insert(node) {
            continue;
        }
        let owner = match node {
            Node::Datatype(Item(owner)) | Node::Impl(Item(owner)) => owner,
        };
        if !super::super::projection_types::ready(tcx, owner) {
            return Err(problem(
                tcx,
                owner.to_def_id(),
                "the original type-dependency owner is unavailable",
            ));
        }
        match node {
            Node::Datatype(_) => {
                // Retain original clauses and fields, before any normalization.
                for (clause, _) in tcx.clauses_of(owner).clauses {
                    build.native(node, *clause, owner.to_def_id())?;
                }
                for field in tcx.adt_def(owner).all_fields() {
                    build.native(
                        node,
                        tcx.type_of(field.did)
                            .instantiate_identity()
                            .skip_normalization(),
                        owner.to_def_id(),
                    )?;
                }
            }
            Node::Impl(_) => {
                if let Some(refusal) =
                    associated_types::impl_problem(tcx, owner, cx.opts.no_external_by_default)
                {
                    return Err(refusal);
                }
                let reference = tcx
                    .impl_trait_ref(owner)
                    .instantiate_identity()
                    .skip_normalization();
                for ty in reference.args.types() {
                    build.native(node, ty, owner.to_def_id())?;
                }
                for member in tcx.associated_items(owner).in_definition_order() {
                    build.native(
                        node,
                        tcx.type_of(member.def_id)
                            .instantiate_identity()
                            .skip_normalization(),
                        owner.to_def_id(),
                    )?;
                }
            }
        }
        if !super::super::projection_types::ready(tcx, owner) {
            return Err(problem(
                tcx,
                owner.to_def_id(),
                "the original type-dependency owner became unavailable",
            ));
        }
    }
    let graph_cost = build
        .edges
        .len()
        .checked_mul(4)
        .and_then(|nodes| {
            build.edges.values().try_fold(nodes, |cost, next| {
                cost.checked_add(next.len().checked_mul(4)?)
            })
        })
        .ok_or_else(|| problem(tcx, origin, "native dependency graph size overflow"))?;
    charge(build.work, graph_cost, tcx, origin)?;
    for component in super::strongly_connected(&build.edges) {
        let cyclic = component.len() > 1
            || build
                .edges
                .get(&component[0])
                .is_some_and(|next| next.contains(&component[0]));
        if cyclic {
            if let Some(Node::Impl(Item(owner))) =
                component.iter().find(|node| matches!(node, Node::Impl(_)))
            {
                return Ok(Some(UserError::new(
                    super::Phase::Simplify,
                    tcx.def_span(*owner),
                    super::messages::TRAIT_CYCLE,
                )));
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
