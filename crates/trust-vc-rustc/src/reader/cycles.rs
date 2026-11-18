//! Cycles through functions, traits and trait implementations.
//!
//! Verus rejects a crate whose functions, traits and trait implementations
//! depend on each other in a cycle: a function without `decreases` that
//! reaches itself ("recursive function must have a decreases clause"), or a
//! cycle through a trait or an implementation ("found a cyclic
//! self-reference in a definition, which may result in nontermination").
//! The graph follows `vir/src/recursion.rs` (`add_call_graph_edges`) and
//! `vir/src/recursive_types.rs` (`add_trait_to_graph`,
//! `add_trait_impl_to_graph`):
//!
//! * a function depends on every function its clauses and body call (a
//!   trait method call at concrete types on the method rustc resolves it
//!   to; an instance also on its generic function), and on the trait
//!   implementations that satisfy the callee's bounds at the call;
//! * a function depends on the traits bounding its type parameters (a trait
//!   method declaration not on its own trait's `Self` bound);
//! * a trait depends on its supertraits and on each of its methods;
//! * an implementation depends on its trait, on the implementations that
//!   satisfy the trait's bounds at the implementing type, and on each of its
//!   methods;
//! * a method implementing a trait method depends on the trait, and on the
//!   spec methods of the implementations it depends on (their definitions
//!   may be needed to prove its clauses);
//! * a default method an implementation inherits is Verus's copy of it for
//!   the implementation (`vir/src/traits.rs`, `inherit_default_bodies`),
//!   which every call of it at the implementing type calls: the
//!   implementation depends on the copy, the copy on the trait, on the
//!   bounds, and on what the default method calls, a call of a method of the
//!   same trait at `Self` taken as a call of the implementation's;
//! * a function that calls a method of an implementation (a copy included)
//!   depends on the implementation, unless the implementation reaches the
//!   function already (`vir/src/context.rs`, `GlobalCtx::new`).
//!
//! Some of these edges approximate Verus's graph: those of instances (Verus
//! has the generic function or the copy), of the clauses an implementation
//! inherits, of implementations assumed for a bound on a type built from
//! type parameters, and between the methods of implementations that depend
//! on each other. The other edges are Verus's own, so a cycle through a trait
//! or an implementation among them alone is Verus's error, reported where
//! Verus's search meets it first. Any other cycle through a trait or an
//! implementation is refused (`trait-cycle`). A cycle of calls alone that
//! Verus has too is a group of recursive functions ([`RecGroup`]), whose
//! termination the VC generator checks, or Verus's error for the functions
//! on it without `decreases`; a cycle through a `decreases_by` function is
//! Verus's error; any other cycle of calls is refused (`recursion`).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self as mty, TyCtxt};

use trust_vc_vcir::{
    Body, DefOrder, Expr, ExprKind, FnDecl, FnId, FnRole, Mode, RecGroup, SpanId, Stmt, StmtKind,
    Ty, VcCrate,
};

use super::{Cx, Refusal, UserError};
use crate::messages::{self, Phase};

mod associated_types;

/// Rebuild the actual raw declaration/selected-implementation graph before
/// datatype base-case reasoning. This exposes diagnostics, never a reusable
/// success certificate or an imported/native ownership capability.
pub(super) fn associated_datatypes(
    cx: &Cx<'_>,
    adts: &[(LocalDefId, &trust_vc_vcir::AdtDecl)],
    items: &[LocalDefId],
) -> Result<Option<UserError>, Refusal> {
    let mut work = cx.projection_type_work.get();
    let result = associated_types::find_with_work(cx, adts, items, &mut work);
    cx.projection_type_work.set(work);
    result
}

/// Preserve the existing trait-dependency traversal grant for both graphs.
const MAX_BOUND_DEPENDENCIES: usize = 10_000;

pub(super) fn type_dependency_work() -> usize { MAX_BOUND_DEPENDENCIES }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Fun(FnId),
    /// Verus's copy of a default method for an implementation that inherits
    /// it (`vir/src/traits.rs`, `inherit_default_bodies`): the
    /// implementation, then the default method. Every instance of the
    /// default method at a type the implementation covers is this node.
    Copy(LocalDefId, LocalDefId),
    Trait(LocalDefId),
    Impl(LocalDefId),
}

impl Node {
    fn key(self) -> (u8, u64, u64) {
        let index = |d: LocalDefId| u64::from(d.local_def_index.as_u32());
        match self {
            Self::Fun(id) => (0, id.0.hi, id.0.lo),
            Self::Copy(imp, method) => (1, index(imp), index(method)),
            Self::Trait(d) => (2, index(d), 0),
            Self::Impl(d) => (3, index(d), 0),
        }
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

/// A trait or implementation, ordered by its index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Item(pub(crate) LocalDefId);

impl PartialOrd for Item {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Item {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .local_def_index
            .as_u32()
            .cmp(&other.0.local_def_index.as_u32())
    }
}

/// What the cycle check found.
#[derive(Default)]
pub(crate) struct Cycles {
    /// Cycles the reader does not decide.
    pub refusals: Vec<Refusal>,
    /// Verus's errors for cycles through traits and for recursion without
    /// `decreases`.
    pub errors: Vec<UserError>,
    /// The spec definitions each function Verus checks may not see
    /// ([`VcCrate::def_order`]).
    pub def_order: BTreeMap<FnId, BTreeMap<FnId, DefOrder>>,
    /// The groups of recursive functions ([`VcCrate::rec_groups`]).
    pub groups: Vec<RecGroup>,
}

/// Every cycle among the functions of `krate`: Verus's error for a cycle
/// through a trait or an implementation that Verus has too, and for a cycle
/// of calls Verus has too with functions that lack `decreases`
/// (`vir/src/recursion.rs`, `check_termination` and
/// `rewrite_spec_recursive_fun_with_fueled_rec_call`: "recursive function
/// must have a decreases clause"), a group of recursive functions for
/// another cycle of calls Verus has too, a refusal for any other.
pub(crate) fn find<'tcx>(
    cx: &Cx<'tcx>,
    krate: &VcCrate,
    defs: &HashMap<FnId, LocalDefId>,
    instances: &HashMap<FnId, (LocalDefId, mty::GenericArgs<'tcx>)>,
    items: &[LocalDefId],
    order: &HashMap<LocalDefId, usize>,
) -> Cycles {
    match associated_types::find(cx, krate, items) {
        Ok(Some(error)) => {
            return Cycles {
                errors: vec![error],
                ..Cycles::default()
            };
        }
        Err(problem) => {
            return Cycles {
                refusals: vec![problem],
                ..Cycles::default()
            };
        }
        Ok(None) => {}
    }
    let tcx = cx.tcx;
    let loose = cx.opts.no_external_by_default;
    // Every edge, and the edges Verus's graph has as well (`exact`): the
    // graph without the reader's own approximations (instances, inherited
    // clauses, implementations assumed for bounds on types built from type
    // parameters, and the requires/ensures dependencies between
    // implementations).
    let edges: RefCell<BTreeMap<Node, BTreeSet<Node>>> = RefCell::new(BTreeMap::new());
    let exact: RefCell<BTreeMap<Node, BTreeSet<Node>>> = RefCell::new(BTreeMap::new());
    let add = |from: Node, to: Node| {
        edges.borrow_mut().entry(from).or_default().insert(to);
    };
    let add_exact = |from: Node, to: Node| {
        add(from, to);
        exact.borrow_mut().entry(from).or_default().insert(to);
    };
    // Where the first edge between two nodes may come among the edges of
    // the first node in Verus's graph (`recursion.rs`, `expand_call_graph`;
    // [`EdgeClass`]): at the earliest, counting the edges Verus may have,
    // and at the latest, counting the edges Verus has. Each occurrence of an
    // edge is given with the classes it may have, and whether Verus has it.
    let edge_class: RefCell<BTreeMap<(Node, Node), EdgeBounds>> = RefCell::new(BTreeMap::new());
    let classify = |from: Node, to: Node, earliest: EdgeClass, latest: EdgeClass, has: bool| {
        let mut classes = edge_class.borrow_mut();
        let entry = classes.entry((from, to)).or_insert(EdgeBounds {
            earliest,
            latest: None,
        });
        entry.earliest = entry.earliest.min(earliest);
        if has {
            entry.latest = Some(entry.latest.map_or(latest, |l| l.min(latest)));
        }
    };
    let fn_ids: HashMap<LocalDefId, FnId> = defs.iter().map(|(id, def)| (*def, *id)).collect();
    let impl_uses = cx.impl_uses.borrow();
    let mut call_sites: HashMap<FnId, BTreeMap<FnId, SpanId>> = HashMap::new();
    // The calls Verus sees in each function: its own clauses and body, not
    // the clauses an implementation inherits (Verus reaches those through
    // the trait); for a copy of a default method, the calls of the default
    // method, redirected to the implementation.
    let mut own_calls: HashMap<Node, BTreeSet<Node>> = HashMap::new();
    // Where each of those calls first is (a span id), for Verus's order.
    let mut call_pos: HashMap<(Node, Node), u32> = HashMap::new();
    let mut out = Cycles::default();
    let inherited = cx.inherited_counts.borrow();
    let mut traits: BTreeSet<Item> = BTreeSet::new();
    let mut impls: BTreeSet<Item> = BTreeSet::new();
    // Verus's copies of default methods: one for every default method of a
    // trait of this crate that an implementation Verus reads does not
    // override, and the one each instance of a default method stands for.
    let mut copies: BTreeSet<(Item, Item)> = BTreeSet::new();
    for item in items {
        match tcx.def_kind(*item) {
            DefKind::Trait => {
                traits.insert(Item(*item));
            }
            DefKind::Impl { .. } => {
                impls.insert(Item(*item));
                for method in inherited_defaults(tcx, *item) {
                    if fn_ids.contains_key(&method) {
                        copies.insert((Item(*item), Item(method)));
                    }
                }
            }
            _ => {}
        }
    }
    // Verus has copies only for the implementations it reads.
    let mut instance_copies: HashMap<FnId, (LocalDefId, LocalDefId)> = HashMap::new();
    for (id, (generic, args)) in instances {
        match inheriting_impl(tcx, *generic, *args) {
            Ok(Some(imp)) if items.contains(&imp) => {
                instance_copies.insert(*id, (imp, *generic));
            }
            Ok(_) => {}
            Err(problem) => {
                out.refusals.push(problem);
                return out;
            }
        }
    }
    copies.extend(
        instance_copies
            .values()
            .map(|(imp, method)| (Item(*imp), Item(*method))),
    );
    let node_of = |id: FnId| match instance_copies.get(&id) {
        Some((imp, method)) => Node::Copy(*imp, *method),
        None => Node::Fun(id),
    };
    // A callee as Verus's graph has it: an instance of a generic function
    // is the generic function, an instance of a default method the copy
    // for its implementation. `None` for an instance Verus has no node for.
    let verus_node = |id: FnId| match instances.get(&id) {
        None => Some(Node::Fun(id)),
        Some((generic, _)) if tcx.def_kind(tcx.local_parent(*generic)) != DefKind::Trait => {
            fn_ids.get(generic).map(|g| Node::Fun(*g))
        }
        Some(_) => instance_copies
            .get(&id)
            .map(|(imp, method)| Node::Copy(*imp, *method)),
    };

    for decl in &krate.fns {
        let me = node_of(decl.id);
        let calls = callees(decl, (0, 0, 0, false));
        for callee in calls.keys() {
            add(me, node_of(*callee));
        }
        call_sites.insert(decl.id, calls);
        let skip = inherited.get(&decl.id).copied().unwrap_or((0, 0, 0, false));
        // The calls and implementations Verus's graph has as well. With a
        // bound on a concrete type in scope, Verus may dispatch a call to
        // another function, through the bound.
        let exact_calls = defs
            .get(&decl.id)
            .is_some_and(|def| !concrete_bound(tcx, *def));
        if defs.contains_key(&decl.id) {
            let mut own: BTreeSet<Node> = BTreeSet::new();
            for_each_call(decl, skip, &mut |callee, _, span, in_clause| {
                if let Some(node) = verus_node(callee) {
                    own.insert(node);
                    let at = call_pos.entry((me, node)).or_insert(span.0);
                    *at = (*at).min(span.0);
                    if exact_calls {
                        let class = if in_clause {
                            EdgeClass::Clause
                        } else {
                            EdgeClass::Body
                        };
                        classify(me, node, class, class, true);
                    }
                }
            });
            // A spec function depends on its `decreases_by` function
            // (`expand_call_graph`), after its bounds and before its calls.
            if let Some(via) = decl.decreases_by {
                own.insert(Node::Fun(via));
                if exact_calls {
                    classify(
                        me,
                        Node::Fun(via),
                        EdgeClass::Bound,
                        EdgeClass::Clause,
                        true,
                    );
                }
                add(me, Node::Fun(via));
            }
            // `extra_dependency`, an edge after the calls, and the calls in
            // values the body discards.
            let extra = cx.extra_deps.borrow();
            let dropped = cx.dropped_calls.borrow();
            let more = extra
                .get(&decl.id)
                .into_iter()
                .chain(dropped.get(&decl.id))
                .flatten();
            for dep in more {
                let Some(node) = verus_node(*dep) else {
                    continue;
                };
                own.insert(node);
                if exact_calls {
                    classify(me, node, EdgeClass::Body, EdgeClass::Body, true);
                }
                add(me, node);
            }
            if exact_calls {
                for callee in &own {
                    add_exact(me, *callee);
                }
            }
            own_calls.insert(me, own);
        }
        for (imp, is_exact) in impl_uses.get(&decl.id).into_iter().flatten() {
            if *is_exact && exact_calls {
                add_exact(me, Node::Impl(imp.0));
            } else {
                add(me, Node::Impl(imp.0));
            }
            classify(
                me,
                Node::Impl(imp.0),
                EdgeClass::Clause,
                EdgeClass::Body,
                *is_exact && exact_calls,
            );
            impls.insert(*imp);
        }
        let def_id = match (defs.get(&decl.id), instances.get(&decl.id)) {
            (Some(def), _) => *def,
            (None, Some((generic, _))) => {
                if let Some(generic_id) = fn_ids.get(generic) {
                    add(me, Node::Fun(*generic_id));
                }
                // A default method inherited by an implementation Verus
                // does not read: a copy would depend on the trait.
                let parent = tcx.local_parent(*generic);
                if matches!(me, Node::Fun(_)) && tcx.def_kind(parent) == DefKind::Trait {
                    add(me, Node::Trait(parent));
                    traits.insert(Item(parent));
                }
                continue;
            }
            (None, None) => continue,
        };
        let parent = tcx.local_parent(def_id);
        // Bounds on the function's type parameters.
        for (clause, _) in tcx.clauses_of(def_id).instantiate_identity(tcx) {
            let mty::ClauseKind::Trait(pred) = clause.skip_normalization().kind().skip_binder()
            else {
                continue;
            };
            let Some(bound) = pred.def_id().as_local() else {
                continue;
            };
            if tcx.def_kind(bound) != DefKind::Trait {
                continue;
            }
            if decl.role == FnRole::TraitDecl && bound == parent && pred.self_ty().is_param(0) {
                continue;
            }
            add_exact(me, Node::Trait(bound));
            classify(
                me,
                Node::Trait(bound),
                EdgeClass::Bound,
                EdgeClass::Bound,
                true,
            );
            traits.insert(Item(bound));
        }
        match tcx.def_kind(parent) {
            DefKind::Trait => {
                add_exact(Node::Trait(parent), me);
                traits.insert(Item(parent));
            }
            DefKind::Impl { of_trait: true } => {
                let trait_id = tcx.impl_trait_id(parent);
                if let Some(trait_id) = trait_id.as_local() {
                    add_exact(me, Node::Trait(trait_id));
                    classify(
                        me,
                        Node::Trait(trait_id),
                        EdgeClass::Trait,
                        EdgeClass::Trait,
                        true,
                    );
                    traits.insert(Item(trait_id));
                }
                add_exact(Node::Impl(parent), me);
                impls.insert(Item(parent));
            }
            _ => {}
        }
    }

    // Verus's copies of default methods (`recursion.rs`,
    // `add_call_graph_edges`, for a `TraitMethodImpl` with
    // `inherit_body_from`): the implementation depends on the copy, the copy
    // on the trait, on the bounds of the implementation and of the default
    // method, and on what the default method calls, a call of a method of
    // the same trait at `Self` redirected to the implementation's
    // (`traits.rs`, `redirect_calls_in_default_methods`).
    for (imp, method) in &copies {
        let (imp, method) = (imp.0, method.0);
        let node = Node::Copy(imp, method);
        let trait_id = tcx.local_parent(method);
        add_exact(Node::Impl(imp), node);
        impls.insert(Item(imp));
        add_exact(node, Node::Trait(trait_id));
        classify(
            node,
            Node::Trait(trait_id),
            EdgeClass::Trait,
            EdgeClass::Trait,
            true,
        );
        traits.insert(Item(trait_id));
        let own_bounds = tcx
            .clauses_of(method)
            .instantiate_identity(tcx)
            .into_iter()
            .map(|(clause, _)| (clause, true));
        let impl_bounds = tcx
            .clauses_of(imp)
            .instantiate_identity(tcx)
            .into_iter()
            .map(|(clause, _)| (clause, false));
        for (clause, of_method) in own_bounds.chain(impl_bounds) {
            let mty::ClauseKind::Trait(pred) = clause.skip_normalization().kind().skip_binder()
            else {
                continue;
            };
            let Some(bound) = pred.def_id().as_local() else {
                continue;
            };
            if tcx.def_kind(bound) != DefKind::Trait {
                continue;
            }
            // `Self: T` itself (`remove_self_is_itself_bound`).
            if of_method && bound == trait_id && pred.self_ty().is_param(0) {
                continue;
            }
            add_exact(node, Node::Trait(bound));
            classify(
                node,
                Node::Trait(bound),
                EdgeClass::Bound,
                EdgeClass::Bound,
                true,
            );
            traits.insert(Item(bound));
        }
        let Some(method_id) = fn_ids.get(&method) else {
            continue;
        };
        add(node, Node::Fun(*method_id));
        let Some(method_decl) = krate.fn_decl(*method_id) else {
            continue;
        };
        let exact_method = !concrete_bound(tcx, method);
        let trait_params = type_param_count(tcx, trait_id);
        let mut calls: BTreeSet<Node> = BTreeSet::new();
        let mut unknown = false;
        let mut positions: Vec<(Node, u32, bool)> = Vec::new();
        let mut other_calls: Vec<Node> = Vec::new();
        for_each_call(
            method_decl,
            (0, 0, 0, false),
            &mut |callee, tys, span, clause| {
                let same_trait = defs.get(&callee).is_some_and(|def| {
                    instances.get(&callee).is_none() && tcx.local_parent(*def) == trait_id
                });
                if !same_trait {
                    match verus_node(callee) {
                        Some(target) => {
                            calls.insert(target);
                            positions.push((target, span.0, clause));
                        }
                        None => unknown = true,
                    }
                    return;
                }
                let at_self = tys.len() >= trait_params
                    && tys[..trait_params]
                        .iter()
                        .enumerate()
                        .all(|(i, t)| *t == Ty::Param(u32::try_from(i).unwrap_or(u32::MAX)));
                if !at_self {
                    // Verus rejects the copy ("call from trait default method to
                    // same trait with different type arguments is not allowed")
                    // or stops earlier; the call dispatches through the
                    // declaration.
                    other_calls.push(Node::Fun(callee));
                    unknown = true;
                    return;
                }
                let callee_def = defs[&callee];
                let implementing = tcx
                    .associated_items(imp)
                    .in_definition_order()
                    .find(|item| item.trait_item_def_id() == Some(callee_def.to_def_id()))
                    .and_then(|item| item.def_id.as_local());
                let target = match implementing {
                    Some(own) => match fn_ids.get(&own) {
                        Some(id) => Node::Fun(*id),
                        None => {
                            unknown = true;
                            return;
                        }
                    },
                    None => Node::Copy(imp, callee_def),
                };
                calls.insert(target);
                positions.push((target, span.0, clause));
            },
        );
        for (target, at, in_clause) in positions {
            let first = call_pos.entry((node, target)).or_insert(at);
            *first = (*first).min(at);
            if exact_method {
                let class = if in_clause {
                    EdgeClass::Clause
                } else {
                    EdgeClass::Body
                };
                classify(node, target, class, class, true);
            }
        }
        for callee in &calls {
            if exact_method {
                add_exact(node, *callee);
            } else {
                add(node, *callee);
            }
        }
        for callee in other_calls {
            add(node, callee);
        }
        if !unknown {
            own_calls.insert(node, calls);
        }
        for (dep, is_exact) in impl_uses.get(method_id).into_iter().flatten() {
            if *is_exact && exact_method {
                add_exact(node, Node::Impl(dep.0));
            } else {
                add(node, Node::Impl(dep.0));
            }
            classify(
                node,
                Node::Impl(dep.0),
                EdgeClass::Clause,
                EdgeClass::Body,
                *is_exact && exact_method,
            );
            impls.insert(*dep);
        }
    }

    // The methods of an implementation, its copies of default methods
    // included, each with its mode.
    let impl_members = |imp: LocalDefId| {
        let own = methods_of(tcx, imp).into_iter().filter_map(|method| {
            let id = fn_ids.get(&method)?;
            Some((Node::Fun(*id), krate.fn_decl(*id)?.mode))
        });
        let inherited = copies
            .iter()
            .filter(move |(i, _)| i.0 == imp)
            .filter_map(|(_, method)| {
                let id = fn_ids.get(&method.0)?;
                Some((Node::Copy(imp, method.0), krate.fn_decl(*id)?.mode))
            });
        own.chain(inherited).collect::<Vec<_>>().into_iter()
    };
    // Implementations reached only through their methods still depend on
    // their trait and on the implementations of its bounds.
    let mut pending: Vec<LocalDefId> = impls.iter().map(|i| i.0).collect();
    let mut seen_impls: BTreeSet<Item> = BTreeSet::new();
    // Verus's path from a method of an implementation to the spec methods
    // of the implementations its trait's bounds need (`recursion.rs`,
    // `expand_call_graph`, and `recursive_types.rs`,
    // `add_trait_impl_to_graph`: `f --> TraitReqEns(D: T, false) -->
    // TraitReqEns(D': T', true) --> f'`), as a direct edge, with the place of
    // the edge among the method's: after its trait, the implementations in
    // the order the bounds need them, their methods in crate order.
    let mut req_ens: BTreeMap<(Node, Node), Vec<u64>> = BTreeMap::new();
    let member_key = |node: Node| match node {
        Node::Fun(id) => [
            0,
            defs.get(&id)
                .and_then(|d| order.get(d))
                .map_or(u64::MAX, |p| *p as u64),
        ],
        Node::Copy(_, method) => [1, order.get(&method).map_or(u64::MAX, |p| *p as u64)],
        Node::Trait(_) | Node::Impl(_) => [2, 0],
    };
    while let Some(imp) = pending.pop() {
        if !seen_impls.insert(Item(imp)) {
            continue;
        }
        let trait_ref = tcx
            .impl_trait_ref(imp)
            .instantiate_identity()
            .skip_normalization();
        if let Some(trait_id) = trait_ref.def_id.as_local() {
            add_exact(Node::Impl(imp), Node::Trait(trait_id));
            traits.insert(Item(trait_id));
        }
        let deps = match bound_impls(
            tcx,
            trait_ref.def_id,
            trait_ref.args,
            None,
            Some(imp.to_def_id()),
        ) {
            Ok(deps) => deps,
            Err(problem) => {
                out.refusals.push(problem);
                return out;
            }
        };
        for (rank, (dep, is_exact)) in deps.into_iter().enumerate() {
            // The implementation satisfies its own trait's `Self` bound.
            if dep == imp {
                continue;
            }
            if is_exact {
                add_exact(Node::Impl(imp), Node::Impl(dep));
            } else {
                add(Node::Impl(imp), Node::Impl(dep));
            }
            // The spec methods of `dep` (its copies of default methods
            // included) may define what this implementation's clauses
            // mention.
            for (spec, _) in impl_members(dep).filter(|(_, mode)| *mode == Mode::Spec) {
                for (own, _) in impl_members(imp) {
                    add(own, spec);
                    classify(own, spec, EdgeClass::ReqEns, EdgeClass::ReqEns, is_exact);
                    if is_exact {
                        let mut key = vec![rank as u64];
                        key.extend(member_key(spec));
                        req_ens.entry((own, spec)).or_insert(key);
                    }
                }
            }
            pending.push(dep);
        }
    }
    // A trait depends on the traits bounding `Self` (supertraits) and its
    // type parameters, transitively.
    let mut pending: Vec<LocalDefId> = traits.iter().map(|t| t.0).collect();
    let mut seen_traits: BTreeSet<Item> = BTreeSet::new();
    while let Some(trait_id) = pending.pop() {
        if !seen_traits.insert(Item(trait_id)) {
            continue;
        }
        let clauses = tcx
            .explicit_super_clauses_of(trait_id)
            .skip_binder()
            .iter()
            .chain(tcx.explicit_clauses_of(trait_id).clauses);
        for (clause, _) in clauses {
            if let mty::ClauseKind::Trait(pred) = clause.kind().skip_binder() {
                // The trait's own `Self` bound is not a dependency
                // (`remove_self_is_itself_bound`).
                if pred.def_id() == trait_id.to_def_id() && pred.self_ty().is_param(0) {
                    continue;
                }
                if let Some(bound) = pred.def_id().as_local() {
                    if super::is_verus_trait(tcx, bound.to_def_id(), loose) {
                        add_exact(Node::Trait(trait_id), Node::Trait(bound));
                        pending.push(bound);
                    }
                }
            }
        }
    }

    // Verus's final call graph (`context.rs`, `GlobalCtx::new`): a function
    // that calls a method of a trait implementation (a copy of a default
    // method included) depends on the implementation too, unless the
    // implementation reaches the function already. Verus decides that in
    // its graph without these edges. Where the exact graph and the whole
    // graph agree the edge is Verus's; where only the whole graph reaches,
    // Verus may lack the edge, which only the whole graph gets.
    let direct: BTreeSet<(Node, Node)> = {
        let impl_of = |node: Node| -> Option<LocalDefId> {
            let def = match node {
                Node::Copy(imp, _) => return Some(imp),
                Node::Fun(id) => defs
                    .get(&id)
                    .copied()
                    .or_else(|| instances.get(&id).map(|(generic, _)| *generic))?,
                Node::Trait(_) | Node::Impl(_) => return None,
            };
            let parent = tcx.local_parent(def);
            if tcx.def_kind(parent) != (DefKind::Impl { of_trait: true }) {
                return None;
            }
            let trait_id = tcx.impl_trait_id(parent);
            super::is_verus_trait(tcx, trait_id, loose).then_some(parent)
        };
        let whole_before = edges.borrow().clone();
        let exact_before = exact.borrow().clone();
        let mut reach_whole: HashMap<LocalDefId, BTreeSet<Node>> = HashMap::new();
        let mut reach_exact: HashMap<LocalDefId, BTreeSet<Node>> = HashMap::new();
        let mut direct = BTreeSet::new();
        for (graph, is_exact) in [(&exact_before, true), (&whole_before, false)] {
            for (from, targets) in graph {
                if !matches!(from, Node::Fun(_) | Node::Copy(..)) {
                    continue;
                }
                for imp in targets.iter().filter_map(|t| impl_of(*t)) {
                    let reached_exact = reach_exact
                        .entry(imp)
                        .or_insert_with(|| reachable(&exact_before, Node::Impl(imp)))
                        .contains(from);
                    if reached_exact {
                        continue;
                    }
                    let reached_whole = reach_whole
                        .entry(imp)
                        .or_insert_with(|| reachable(&whole_before, Node::Impl(imp)))
                        .contains(from);
                    let has = is_exact && !reached_whole;
                    if has {
                        add_exact(*from, Node::Impl(imp));
                    } else {
                        add(*from, Node::Impl(imp));
                    }
                    classify(
                        *from,
                        Node::Impl(imp),
                        EdgeClass::Final,
                        EdgeClass::Final,
                        has,
                    );
                    direct.insert((*from, Node::Impl(imp)));
                }
            }
        }
        direct
    };

    let edges = edges.into_inner();
    let exact = exact.into_inner();
    // The traits and implementations on a cycle of Verus's graph.
    let exact_cyclic: BTreeSet<Node> = strongly_connected(&exact)
        .into_iter()
        .filter(|c| c.len() > 1 || exact.get(&c[0]).is_some_and(|next| next.contains(&c[0])))
        .flatten()
        .filter(|n| matches!(n, Node::Trait(_) | Node::Impl(_)))
        .collect();
    let ordered = Ordered::new(
        tcx,
        &exact,
        &direct,
        defs,
        krate,
        order,
        &call_pos,
        &BTreeMap::new(),
    );
    let mut first_trait_cycle: Option<(usize, UserError)> = None;
    for component in strongly_connected(&edges) {
        let cyclic = component.len() > 1
            || edges
                .get(&component[0])
                .is_some_and(|next| next.contains(&component[0]));
        if !cyclic {
            continue;
        }
        let through_traits = component
            .iter()
            .any(|n| matches!(n, Node::Trait(_) | Node::Impl(_)));
        let names: Vec<String> = component
            .iter()
            .filter_map(|n| match n {
                Node::Fun(id) => krate.fn_decl(*id).map(|d| format!("`{}`", d.name)),
                Node::Copy(imp, method) => Some(format!(
                    "`{}` inherited by `{}`",
                    tcx.def_path_str(method.to_def_id()),
                    tcx.def_path_str(imp.to_def_id())
                )),
                _ => None,
            })
            .collect();
        let def_span = component
            .iter()
            .find_map(|n| match n {
                Node::Fun(id) => defs
                    .get(id)
                    .copied()
                    .or_else(|| instances.get(id).map(|(d, _)| *d)),
                Node::Copy(_, method) => Some(*method),
                Node::Trait(d) | Node::Impl(d) => Some(*d),
            })
            .map_or(rustc_span::DUMMY_SP, |d| tcx.def_span(d));
        // Verus's error, when its graph has a cycle through one of the
        // component's traits or implementations (`recursive_types.rs`,
        // `check_traits`, before simplification). Verus reports the first
        // cycle it meets and stops; the others are not reported.
        if through_traits && component.iter().any(|n| exact_cyclic.contains(n)) {
            let members: BTreeSet<Node> = component.iter().copied().collect();
            if let Some((rank, function)) = ordered.first_cycle(&members) {
                let at = function.map_or(def_span, |d| super::sig_span(tcx, d));
                let mut error = UserError::new(Phase::Simplify, at, messages::TRAIT_CYCLE);
                error.function = function;
                if first_trait_cycle.as_ref().is_none_or(|(r, _)| rank < *r) {
                    first_trait_cycle = Some((rank, error));
                }
                continue;
            }
        }
        if through_traits {
            out.refusals.push(Refusal::new(
                "trait-cycle",
                format!(
                    "a cycle through trait definitions and implementations: {}",
                    names.join(", ")
                ),
                def_span,
            ));
            continue;
        }
        let nodes: BTreeSet<Node> = component.iter().copied().collect();
        let members: BTreeSet<FnId> = component
            .iter()
            .filter_map(|n| match n {
                Node::Fun(id) => Some(*id),
                _ => None,
            })
            .collect();
        if members.iter().any(|id| {
            krate
                .fn_decl(*id)
                .is_some_and(|decl| decl.attrs.broadcast_triggers.is_some())
        }) {
            out.refusals.push(Refusal::new(
                "broadcast-recursion",
                "a cycle through a broadcast proof contract",
                def_span,
            ));
            continue;
        }
        // `context.rs`, `GlobalCtx::new`: a `decreases_by` function on a
        // cycle, reported for the first such function in Verus's order.
        let by_cycle = members.iter().copied().find(|id| {
            krate
                .fn_decl(*id)
                .is_some_and(|decl| decl.attrs.is_decreases_by)
        });
        if let Some(by) = by_cycle {
            if let Some(def) = defs.get(&by) {
                let mut error = UserError::new(
                    Phase::Simplify,
                    tcx.def_span(*def),
                    messages::termination::BY_CYCLE,
                );
                error.function = Some(*def);
                out.errors.push(error);
                continue;
            }
        }
        // A call of an instance of a member is a recursive call in Verus's
        // graph, whose termination VcIR cannot check: an instance is
        // another function there.
        let through_instance = krate.fns.iter().any(|decl| {
            members.contains(&decl.id)
                && callees(decl, (0, 0, 0, false)).keys().any(|callee| {
                    instances.contains_key(callee)
                        && matches!(verus_node(*callee), Some(Node::Fun(g)) if members.contains(&g))
                })
        });
        let recursion = match verus_recursion(tcx, krate, defs, &nodes, &own_calls) {
            Some(Recursion::Group(_)) if through_instance => None,
            other => other,
        };
        match recursion {
            Some(Recursion::Errors(errors)) => {
                out.errors.extend(errors);
                continue;
            }
            Some(Recursion::Group(group)) => {
                out.groups.push(group);
                continue;
            }
            None => {}
        }
        // A cycle of calls: refused at the first call, in crate order, of a
        // function of the cycle by another.
        let site = krate
            .fns
            .iter()
            .filter(|d| members.contains(&d.id))
            .find_map(|d| {
                let calls = call_sites.get(&d.id)?;
                calls
                    .iter()
                    .filter(|(callee, _)| members.contains(callee))
                    .min_by_key(|(_, span)| span.0)
                    .map(|(callee, span)| (*callee, *span))
            });
        let (detail, span) = match site {
            Some((callee, span)) => (
                format!(
                    "a recursive call of `{}`, on a cycle the reader does not model",
                    krate.fn_decl(callee).map_or("?", |d| d.name.as_str())
                ),
                cx.span_of(span).unwrap_or(def_span),
            ),
            None => (
                format!(
                    "recursive functions on a cycle the reader does not model: {}",
                    names.join(", ")
                ),
                def_span,
            ),
        };
        out.refusals.push(Refusal::new("recursion", detail, span));
    }
    out.errors.extend(first_trait_cycle.map(|(_, error)| error));

    // Where each node may come among the nodes of Verus's graph. Verus
    // lists the trait implementations in the order it meets them in the
    // crate (`rust_to_vir.rs`, `crate_to_vir`), as `items` does.
    let impl_rank: HashMap<LocalDefId, u64> = items
        .iter()
        .filter(|item| tcx.def_kind(**item) == (DefKind::Impl { of_trait: true }))
        .enumerate()
        .map(|(rank, item)| (*item, rank as u64))
        .collect();
    let place = |node: Node| -> Place {
        let node = match node {
            Node::Fun(id) if instances.contains_key(&id) => match verus_node(id) {
                Some(node @ Node::Copy(..)) => node,
                // The calls of an instance are its callers' in Verus's
                // graph, which reach what it reaches.
                Some(_) => return Place::Instance,
                None => return Place::Unknown,
            },
            node => node,
        };
        match node {
            Node::Trait(_) => Place::Trait,
            Node::Copy(imp, method) => Place::Copy(
                impl_rank.get(&imp).copied(),
                order.get(&method).map(|p| *p as u64),
            ),
            Node::Impl(imp) => Place::Impl(impl_rank.get(&imp).copied()),
            Node::Fun(id) => {
                let (Some(decl), Some(def)) = (krate.fn_decl(id), defs.get(&id)) else {
                    return Place::Unknown;
                };
                let at = order.get(def).map(|p| *p as u64);
                match (&decl.body, decl.mode) {
                    _ if decl.attrs.external_body => Place::Bodiless(at),
                    (Body::None, _) => Place::Bodiless(at),
                    (Body::Spec(_) | Body::Constant(_), Mode::Spec) => Place::Spec(at),
                    (Body::Stmts(_), Mode::Exec | Mode::Proof) => Place::Other,
                    _ => Place::Unknown,
                }
            }
        }
    };
    // Verus's graph with the paths through `TraitReqEns`, and the order
    // modelled on it.
    let mut verus_graph = exact.clone();
    for (from, to) in req_ens.keys() {
        verus_graph.entry(*from).or_default().insert(*to);
    }
    let model = Ordered::new(
        tcx,
        &verus_graph,
        &direct,
        defs,
        krate,
        order,
        &call_pos,
        &req_ens,
    );
    let edge_class = edge_class.into_inner();
    // Where an edge comes among its source's edges, at the earliest and, when
    // Verus has it, at the latest: a function's by [`EdgeClass`]; an
    // implementation's first to its trait and to the implementations its
    // bounds need (`recursive_types.rs`, `add_trait_impl_to_graph`), then to
    // its methods in crate order, its copies of default methods last
    // (`recursion.rs`, `expand_call_graph`, for each function in turn).
    let position = |def: LocalDefId| order.get(&def).map_or(u64::MAX, |p| *p as u64);
    let edge_key = |from: Node, to: Node| -> (EdgeKey, Option<EdgeKey>) {
        match (from, to) {
            (Node::Fun(_) | Node::Copy(..), _) => match edge_class.get(&(from, to)) {
                Some(bounds) => (
                    (bounds.earliest as u8, 0),
                    bounds.latest.map(|latest| (latest as u8, 0)),
                ),
                None => ((0, 0), None),
            },
            (Node::Impl(_), Node::Trait(_) | Node::Impl(_)) => ((0, 0), Some((0, 0))),
            (Node::Impl(imp), Node::Fun(id))
                if defs
                    .get(&id)
                    .is_some_and(|def| tcx.local_parent(*def) == imp) =>
            {
                let at = (1, position(defs[&id]));
                (at, Some(at))
            }
            (Node::Impl(imp), Node::Copy(of, method)) if of == imp => {
                let at = (2, position(method));
                (at, Some(at))
            }
            _ => ((0, 0), None),
        }
    };
    // The implementations whose trait bound facts guard a spec definition.
    // Verus's definition of a spec method of a trait implementation, and of
    // its copy of a default spec method, holds only where the method's trait
    // bounds hold (`sst_to_air_func.rs`: `func_body_to_air`, `def_reqs`, and
    // `func_axioms_to_air`, the axiom for `inherit_body_from`); the bounds of
    // the copy are the default method's, its trait's on `Self` included,
    // without `Self: Trait` itself, and its implementation's (`traits.rs`,
    // `inherit_default_bodies`). At a concrete type a bound is the fact an
    // implementation's `Trait-Impl-Axiom` states, which Verus emits after
    // the implementation's component (`commands.rs`, `handle_scc_component`).
    let guarded: Vec<(FnId, LocalDefId, mty::GenericArgs<'_>, Option<_>)> = krate
        .fns
        .iter()
        .filter(|d| d.mode == Mode::Spec && matches!(d.body, Body::Spec(_) | Body::Constant(_)))
        .filter(|d| d.role != FnRole::TraitDecl)
        .filter_map(|d| {
            let (def, args, skip_self) = match instances.get(&d.id) {
                Some((generic, args)) => {
                    let parent = tcx.local_parent(*generic);
                    match tcx.def_kind(parent) {
                        DefKind::Trait => (*generic, *args, Some(parent.to_def_id())),
                        DefKind::Impl { of_trait: true } => (*generic, *args, None),
                        _ => return None,
                    }
                }
                None => {
                    let def = *defs.get(&d.id)?;
                    let parent = tcx.local_parent(def);
                    if tcx.def_kind(parent) != (DefKind::Impl { of_trait: true }) {
                        return None;
                    }
                    let args = mty::GenericArgs::identity_for_item(tcx, def);
                    (def, args, None)
                }
            };
            Some((d.id, def, args, skip_self))
        })
        .collect();
    let mut guards: HashMap<FnId, Vec<(LocalDefId, bool)>> = HashMap::new();
    for (id, def, args, skip_self) in &guarded {
        let needed = match bound_impls(tcx, def.to_def_id(), *args, *skip_self, None) {
            Ok(needed) => needed,
            Err(problem) => {
                out.refusals.push(problem);
                return out;
            }
        };
        let needed: Vec<(LocalDefId, bool)> = needed
            .into_iter()
            .filter(|(imp, _)| super::is_verus_trait(tcx, tcx.impl_trait_id(*imp), loose))
            .collect();
        if !needed.is_empty() {
            guards.insert(*id, needed);
        }
    }
    // The definitions guarded by a bound on concrete types that no
    // implementation meets: a copy of a default method whose own bound
    // (`where Self: Tr`) the implementing type does not meet, which rustc
    // accepts. Verus never states such a bound, so no function sees the
    // definition.
    let never: HashMap<FnId, DefOrder> = guarded
        .iter()
        .filter_map(|(id, def, args, _)| {
            unmet_bound(tcx, def.to_def_id(), *args, None, loose).map(|order| (*id, order))
        })
        .collect();
    // The functions Verus checks with a bound on a concrete type assumed,
    // which may state a guard's fact itself.
    let assumes_concrete: BTreeSet<FnId> = defs
        .iter()
        .filter(|(_, def)| concrete_bound(tcx, **def))
        .map(|(id, _)| *id)
        .collect();
    out.def_order = definition_order(
        krate,
        &edges,
        &verus_graph,
        &edge_key,
        &model,
        &verus_node,
        &place,
        &guards,
        &never,
        &assumes_concrete,
        &out.groups,
    );
    // The definitions a function uses where it lacks their bounds (in the
    // clauses an implementation's method inherits from a trait method whose
    // bounds it does not repeat), found where the function was read.
    for (function, hidden) in cx.bound_hides.borrow().iter() {
        if !krate
            .fn_decl(*function)
            .is_some_and(|d| matches!(d.body, Body::Stmts(_) | Body::Constant(_)))
        {
            continue;
        }
        let orders = out.def_order.entry(*function).or_default();
        for (spec, order) in hidden {
            let merged = match (orders.get(spec), order) {
                (Some(DefOrder::Later), _) | (_, DefOrder::Later) => DefOrder::Later,
                _ => DefOrder::Unknown,
            };
            orders.insert(*spec, merged);
        }
    }
    out
}

/// Where a node of Verus's call graph comes in the order Verus adds the
/// nodes (`context.rs`, `GlobalCtx::new`): the crate, traits with bounds on
/// other traits, functions without a body in crate order (Verus's copies of
/// default methods last, by implementation and then in the order of the
/// trait's methods: `traits.rs`, `inherit_default_bodies`), spec functions
/// in crate order, trait implementations in the order Verus lists them,
/// then the nodes the edges of each function add.
#[derive(Debug, Clone, Copy)]
enum Place {
    /// A trait: added with its bounds, or when an edge first names it.
    Trait,
    /// A function without a body, at its place in crate order.
    Bodiless(Option<u64>),
    /// Verus's copy of a default method for an implementation: a function
    /// without a body, after the others, in the order of the
    /// implementations and then of the trait's methods in crate order.
    Copy(Option<u64>, Option<u64>),
    /// A spec function with a body, at its place in crate order.
    Spec(Option<u64>),
    /// A trait implementation, at its place among the implementations
    /// Verus lists.
    Impl(Option<u64>),
    /// An exec or proof function with a body: added with its edges.
    Other,
    /// An instance of a generic function: not a node of Verus's graph.
    Instance,
    /// Not known: anywhere.
    Unknown,
}

/// A position among Verus's nodes, ordered.
type Rank = (u8, u64, u64);

/// Where an edge comes among the edges of its source: a class
/// ([`EdgeClass`] for a function's) and a place in it.
type EdgeKey = (u8, u64);

/// Where the first edge between two nodes may come among the edges of the
/// first node ([`EdgeClass`]): at the earliest, and at the latest when
/// Verus's graph has the edge.
#[derive(Debug, Clone, Copy)]
struct EdgeBounds {
    earliest: EdgeClass,
    latest: Option<EdgeClass>,
}

/// Where an edge from a function comes among the function's edges in
/// Verus's graph (`recursion.rs`, `expand_call_graph`): its trait, the path
/// through `TraitReqEns`, the traits of its bounds, the calls in its clauses
/// and then in its body (each after the implementations the call needs),
/// and last the implementations of the methods it calls (`context.rs`,
/// `GlobalCtx::new`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EdgeClass {
    Trait,
    ReqEns,
    Bound,
    Clause,
    Body,
    Final,
}

impl Place {
    /// The earliest position the node may have.
    fn low(self) -> Rank {
        match self {
            Self::Unknown => (0, 0, 0),
            Self::Trait => (1, 0, 0),
            Self::Bodiless(at) => (2, 0, at.unwrap_or(0)),
            Self::Copy(imp, at) => (2, 1 + imp.unwrap_or(0), at.unwrap_or(0)),
            Self::Spec(at) => (3, at.unwrap_or(0), 0),
            Self::Impl(at) => (4, at.unwrap_or(0), 0),
            Self::Other => (5, 0, 0),
            Self::Instance => (u8::MAX, 0, 0),
        }
    }

    /// The latest position the node may have.
    fn high(self) -> Rank {
        match self {
            Self::Unknown | Self::Trait | Self::Other | Self::Instance => (u8::MAX, 0, 0),
            Self::Bodiless(at) => (2, 0, at.unwrap_or(u64::MAX)),
            Self::Copy(imp, at) => (
                2,
                imp.map_or(u64::MAX, |imp| 1 + imp),
                at.unwrap_or(u64::MAX),
            ),
            Self::Spec(at) => (3, at.unwrap_or(u64::MAX), 0),
            Self::Impl(at) => (4, at.unwrap_or(u64::MAX), 0),
        }
    }

    /// Is a node here added to Verus's graph before one at `later`?
    fn before(self, later: Self) -> bool {
        self.high() < later.low()
    }
}

/// For each function Verus checks, the spec definitions it may not see
/// ([`VcCrate::def_order`]).
///
/// Verus checks a crate one strongly connected component of its call graph
/// at a time, in the order its Tarjan search completes them, and emits the
/// definitions of a component's spec functions after checking the
/// component's functions (`rust_verify/src/commands.rs`,
/// `OpGenerator::handle_scc_component`). A function sees the definitions of
/// the spec functions completed before it.
///
/// A spec function that cannot reach the function (through any edge,
/// `edges`) is completed first when the function reaches it through Verus's
/// edges (`exact`, the paths through `TraitReqEns` included), or when the
/// search meets it before any node that may reach the function: a search
/// starts from each node, in the order Verus adds them ([`Place`]), that an
/// earlier search did not reach, and follows a node's edges in order
/// ([`EdgeClass`], [`EdgeKey`]). That holds for a spec function reached from
/// a node Verus adds before every node that may reach the function, and for
/// one reached through an edge of the first of those nodes that comes before
/// every edge of it towards the function, or, where one edge towards the
/// function comes before all the others, through such an edge of the node
/// it leads to, and so on. It holds as well for one reached through such an
/// edge of a node every path into the function passes through, when Verus
/// adds that node before the nodes on those paths (a trait implementation
/// whose method only it reaches: the search enters it first, and follows its
/// edges to the implementations its bounds need before those to its
/// methods). A spec function that may reach the function is
/// [`DefOrder::Later`]. Any other order depends on the order of the
/// edges, which the reader models only approximately ([`Ordered`]): where the
/// model completes the spec function after the function, the definition is
/// [`DefOrder::Later`]; where it completes it before, [`DefOrder::Unknown`].
///
/// A definition guarded by trait bounds (`guards`: the implementations
/// whose `Trait-Impl-Axiom`s state them, each with whether the
/// implementation is the one the bound needs or only a candidate) is usable
/// only where each of those implementations is completed before the
/// function too, by the same rules; a function with a bound on a concrete
/// type in scope (`assumes_concrete`) may assume a guard's fact itself, so
/// there a guard that is not met makes the order [`DefOrder::Unknown`].
/// A definition guarded by a bound that no implementation meets (`never`,
/// [`unmet_bound`]) takes the order `never` gives it for every function,
/// [`DefOrder::Unknown`] where a function may assume the bound.
#[allow(clippy::too_many_arguments)]
fn definition_order(
    krate: &VcCrate,
    edges: &BTreeMap<Node, BTreeSet<Node>>,
    exact: &BTreeMap<Node, BTreeSet<Node>>,
    edge_key: &dyn Fn(Node, Node) -> (EdgeKey, Option<EdgeKey>),
    ordered: &Ordered,
    verus_node: &dyn Fn(FnId) -> Option<Node>,
    place: &dyn Fn(Node) -> Place,
    guards: &HashMap<FnId, Vec<(LocalDefId, bool)>>,
    never: &HashMap<FnId, DefOrder>,
    assumes_concrete: &BTreeSet<FnId>,
    groups: &[RecGroup],
) -> BTreeMap<FnId, BTreeMap<FnId, DefOrder>> {
    let reverse = |graph: &BTreeMap<Node, BTreeSet<Node>>| {
        let mut out: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
        for (from, targets) in graph {
            for to in targets {
                out.entry(*to).or_default().insert(*from);
            }
        }
        out
    };
    let edges_back = reverse(edges);
    let exact_back = reverse(exact);
    let ranks = ordered.ranks();
    // A node a definition needs completed: the node and the places of the
    // nodes that reach it.
    struct Target {
        node: Node,
        reached_from: Vec<Place>,
    }
    let target = |node: Node| Target {
        node,
        reached_from: reachable(&exact_back, node)
            .into_iter()
            .chain([node])
            .map(place)
            .collect(),
    };
    // A spec function with a definition: Verus's node for it, and the
    // implementations whose bound facts guard the definition, each with
    // whether the bound needs exactly that implementation.
    struct Spec {
        def: Target,
        guards: Vec<(Target, bool)>,
    }
    let specs: Vec<(FnId, Option<Spec>)> = krate
        .fns
        .iter()
        .filter(|d| d.mode == Mode::Spec && matches!(d.body, Body::Spec(_) | Body::Constant(_)))
        .filter(|d| d.role != FnRole::TraitDecl)
        .map(|d| {
            let info = verus_node(d.id).map(|node| Spec {
                def: target(node),
                guards: guards
                    .get(&d.id)
                    .into_iter()
                    .flatten()
                    .map(|(imp, is_exact)| (target(Node::Impl(*imp)), *is_exact))
                    .collect(),
            });
            (d.id, info)
        })
        .collect();
    let mut out = BTreeMap::new();
    for decl in &krate.fns {
        // A recursive spec function's termination is checked too.
        let recursive_spec = decl.mode == Mode::Spec
            && matches!(decl.body, Body::Spec(_))
            && groups.iter().any(|group| group.contains(decl.id));
        let checked = (decl.mode != Mode::Spec
            && matches!(decl.body, Body::Stmts(_))
            && !decl.attrs.external_body
            && decl.role != FnRole::Instance)
            || (matches!(decl.body, Body::Constant(_))
                && !decl.attrs.external_body
                && decl.role != FnRole::Instance)
            || recursive_spec;
        if !checked {
            continue;
        }
        let me = Node::Fun(decl.id);
        let reached = reachable(exact, me);
        // The nodes that may reach this function, and their places.
        let towards: BTreeSet<Node> = reachable(&edges_back, me).into_iter().chain([me]).collect();
        let reached_from: Vec<Place> = towards.iter().map(|n| place(*n)).collect();
        // What the search meets before it meets a node that may reach this
        // function: the first of those nodes Verus adds starts a search,
        // which follows its edges in order. Where one edge towards the
        // function comes before all the others, the search follows it next.
        let first = towards.iter().copied().find(|first| {
            towards
                .iter()
                .all(|other| other == first || place(*first).before(place(*other)))
        });
        // What the search meets at `node` before its first edge towards this
        // function: the nodes that Verus's edges coming before every such
        // edge lead to, and what they reach. Returns the edges towards the
        // function.
        let meet_at = |node: Node, met: &mut BTreeSet<Node>| {
            let onward: Vec<(Node, EdgeKey, Option<EdgeKey>)> = edges
                .get(&node)
                .into_iter()
                .flatten()
                .filter(|next| towards.contains(next))
                .map(|next| {
                    let (earliest, latest) = edge_key(node, *next);
                    (*next, earliest, latest)
                })
                .collect();
            let towards_first = onward.iter().map(|(_, earliest, _)| *earliest).min();
            for next in exact.get(&node).into_iter().flatten() {
                if towards.contains(next) {
                    continue;
                }
                let Some(latest) = edge_key(node, *next).1 else {
                    continue;
                };
                if towards_first.is_none_or(|key| latest < key) {
                    met.insert(*next);
                    met.extend(reachable(exact, *next));
                }
            }
            onward
        };
        let mut met_first: BTreeSet<Node> = BTreeSet::new();
        let mut entered: BTreeSet<Node> = BTreeSet::new();
        let mut current = first;
        while let Some(node) = current.take() {
            if node == me || !entered.insert(node) {
                break;
            }
            let onward = meet_at(node, &mut met_first);
            current = onward
                .iter()
                .find(|(next, _, latest)| {
                    exact.get(&node).is_some_and(|out| out.contains(next))
                        && latest.is_some_and(|latest| {
                            onward
                                .iter()
                                .all(|(other, earliest, _)| other == next || latest < *earliest)
                        })
                })
                .map(|(next, _, _)| *next);
        }
        // A node every path into this function passes through, added before
        // every node between it and the function, is entered before the
        // function is: what it meets before its edges towards the function
        // is completed first. Such nodes are followed upwards from the
        // function while each is the only node with an edge into the one
        // below it.
        let mut below: Vec<Node> = vec![me];
        while let Some(lowest) = below.last().copied() {
            let mut into = edges_back
                .get(&lowest)
                .into_iter()
                .flatten()
                .filter(|n| **n != lowest);
            let (Some(through), None) = (into.next().copied(), into.next()) else {
                break;
            };
            if below.contains(&through) || !below.iter().all(|n| place(through).before(place(*n))) {
                break;
            }
            meet_at(through, &mut met_first);
            below.push(through);
        }
        // Where `target` is completed relative to this function: before it
        // (`None`), or the definition's order.
        let completed = |target: &Target| -> Option<DefOrder> {
            // A node that may reach this function may be completed with it,
            // in one component, or after it.
            let may_reach = towards.contains(&target.node);
            if !may_reach
                && (reached.contains(&target.node)
                    || met_first.contains(&target.node)
                    || target
                        .reached_from
                        .iter()
                        .any(|first| reached_from.iter().all(|other| first.before(*other))))
            {
                None
            } else if may_reach || reached.contains(&target.node) {
                Some(DefOrder::Later)
            } else {
                match (ranks.get(&target.node), ranks.get(&me)) {
                    (Some(node_rank), Some(rank)) if node_rank < rank => Some(DefOrder::Unknown),
                    (Some(_), Some(_)) => Some(DefOrder::Later),
                    _ => Some(DefOrder::Unknown),
                }
            }
        };
        let mut unseen = BTreeMap::new();
        for (spec, info) in &specs {
            let Some(info) = info else {
                unseen.insert(*spec, DefOrder::Unknown);
                continue;
            };
            let mut order = completed(&info.def);
            // A bound no implementation meets; a function with a bound on a
            // concrete type in scope may assume it.
            match never.get(spec) {
                Some(DefOrder::Later) if !assumes_concrete.contains(&decl.id) => {
                    order = Some(DefOrder::Later);
                }
                Some(_) if order.is_none() => order = Some(DefOrder::Unknown),
                _ => {}
            }
            for (guard, is_exact) in &info.guards {
                let needed = match completed(guard) {
                    Some(DefOrder::Later) if !is_exact || assumes_concrete.contains(&decl.id) => {
                        Some(DefOrder::Unknown)
                    }
                    other => other,
                };
                order = match (order, needed) {
                    (Some(DefOrder::Later), _) | (_, Some(DefOrder::Later)) => {
                        Some(DefOrder::Later)
                    }
                    (Some(DefOrder::Unknown), _) | (_, Some(DefOrder::Unknown)) => {
                        Some(DefOrder::Unknown)
                    }
                    (None, None) => None,
                };
            }
            if let Some(order) = order {
                unseen.insert(*spec, order);
            }
        }
        if !unseen.is_empty() {
            out.insert(decl.id, unseen);
        }
    }
    out
}

/// Does a bound on a concrete type (an implementation's where clause) hold
/// in `def`? Verus then dispatches a call rustc resolves through it to the
/// trait's declaration, which is not the call this graph holds.
fn concrete_bound(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    tcx.clauses_of(def)
        .instantiate_identity(tcx)
        .into_iter()
        .any(|(clause, _)| {
            matches!(clause.skip_normalization().kind().skip_binder(),
                mty::ClauseKind::Trait(pred) if !pred.self_ty().has_param())
        })
}

/// What Verus does with a cycle of calls it has too.
enum Recursion {
    /// "recursive function must have a decreases clause", for each member
    /// that needs termination checked and has no measure.
    Errors(Vec<UserError>),
    /// Every member that needs a measure has one: a group of recursive
    /// functions, each with the length of its shortest cycle.
    Group(RecGroup),
}

/// The cycle of calls `members`, when Verus has the same cycle (the members
/// call each other through the calls Verus sees alone, and each is a
/// function Verus has: a function of the crate or Verus's copy of a default
/// method, not an instance). A member with a body needs termination
/// checked unless it is an exec function with
/// `exec_allows_no_decreases_clause` or `assume_termination`
/// (`check_termination`); one without a measure is Verus's error (a copy
/// or an `external_body` function has no body of its own, so it has none). `None`
/// when the cycle is not decided that way, or holds what the reader does
/// not model as recursion (a copy, a trait method declaration).
fn verus_recursion(
    tcx: TyCtxt<'_>,
    krate: &VcCrate,
    defs: &HashMap<FnId, LocalDefId>,
    members: &BTreeSet<Node>,
    own_calls: &HashMap<Node, BTreeSet<Node>>,
) -> Option<Recursion> {
    for member in members {
        let def = match member {
            Node::Fun(id) => *defs.get(id)?,
            Node::Copy(_, method) => *method,
            Node::Trait(_) | Node::Impl(_) => return None,
        };
        if concrete_bound(tcx, def) {
            return None;
        }
    }
    // Strongly connected through their own calls alone.
    let mut own: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
    for member in members {
        let calls = own_calls.get(member)?;
        own.insert(
            *member,
            calls
                .iter()
                .filter(|c| members.contains(c))
                .copied()
                .collect(),
        );
    }
    let components = strongly_connected(&own);
    let whole = components.iter().any(|c| c.len() == members.len());
    let single = members.len() == 1
        && members
            .iter()
            .next()
            .is_some_and(|m| own_calls.get(m).is_some_and(|c| c.contains(m)));
    if !(whole && (members.len() > 1 || single)) {
        return None;
    }
    let mut errors = Vec::new();
    for member in members {
        let Node::Fun(id) = member else {
            continue;
        };
        let def = defs[id];
        let decl = krate.fn_decl(*id)?;
        let exec_allowed = decl.mode == Mode::Exec && decl.attrs.exec_allows_no_decreases;
        // `check_termination` runs on bodies; an `external_body` function
        // has none.
        let bodiless = decl.attrs.external_body || matches!(decl.body, Body::None);
        if exec_allowed || bodiless || !decl.decreases.is_empty() {
            continue;
        }
        let mut error = UserError::new(
            Phase::Sst,
            super::sig_span(tcx, def),
            messages::RECURSION_WITHOUT_DECREASES,
        );
        if decl.mode == Mode::Exec {
            error.help = Some(messages::RECURSION_WITHOUT_DECREASES_EXEC_HELP.to_string());
        }
        error.function = Some(def);
        errors.push(error);
    }
    if !errors.is_empty() {
        return Some(Recursion::Errors(errors));
    }
    let mut group = Vec::new();
    for member in members {
        let Node::Fun(id) = member else {
            return None;
        };
        if krate.fn_decl(*id)?.role != FnRole::Item {
            return None;
        }
        let cycle = shortest_cycle_len(&own, *member)?;
        group.push((*id, u32::try_from(cycle).ok()?));
    }
    Some(Recursion::Group(RecGroup { members: group }))
}

/// The length of the shortest cycle of `graph` from `start` back to itself
/// (`scc.rs`, `shortest_cycle_back_to_self`), breadth first.
fn shortest_cycle_len(graph: &BTreeMap<Node, BTreeSet<Node>>, start: Node) -> Option<usize> {
    let mut frontier = vec![start];
    let mut reached: BTreeSet<Node> = BTreeSet::new();
    for length in 1..=graph.len() {
        let mut next = Vec::new();
        for node in frontier {
            for succ in graph.get(&node).into_iter().flatten() {
                if *succ == start {
                    return Some(length);
                }
                if reached.insert(*succ) {
                    next.push(*succ);
                }
            }
        }
        frontier = next;
    }
    None
}

/// The functions `decl` calls in its clauses and body, each with its first
/// call in program order; `skip` leading `requires`, `ensures` and
/// `recommends` clauses are left out.
fn callees(decl: &FnDecl, skip: (usize, usize, usize, bool)) -> BTreeMap<FnId, SpanId> {
    let mut out = BTreeMap::new();
    for_each_call(decl, skip, &mut |callee, _, span, _| {
        out.entry(callee).or_insert(span);
    });
    out
}

/// What [`for_each_call`] calls for each call: the callee, its type
/// arguments, where the call is, and whether it is in a clause.
type CallVisitor<'v> = dyn FnMut(FnId, &[Ty], SpanId, bool) + 'v;

/// Every call in `decl`'s clauses and body, in program order, with its type
/// arguments and whether it is in a clause; `skip` leading `requires`,
/// `ensures` and `recommends` clauses are left out.
fn for_each_call(decl: &FnDecl, skip: (usize, usize, usize, bool), f: &mut CallVisitor<'_>) {
    for hint in decl.broadcast_hints() {
        expr_calls(hint, &mut |callee, args, span| f(callee, args, span, true));
    }
    for clause in decl
        .requires
        .iter()
        .skip(skip.0)
        .chain(decl.ensures.iter().skip(skip.1))
        .chain(decl.recommends.iter().skip(skip.2))
    {
        expr_calls(&clause.expr, &mut |callee, args, span| {
            f(callee, args, span, true)
        });
    }
    for measure in decl.decreases.iter().chain(&decl.decreases_when) {
        expr_calls(measure, &mut |callee, args, span| {
            f(callee, args, span, true)
        });
    }
    if let Some(condition) = decl
        .unwind
        .as_ref()
        .and_then(trust_vc_vcir::UnwindSpec::condition)
        .filter(|_| !skip.3)
    {
        expr_calls(condition, &mut |callee, args, span| {
            f(callee, args, span, true)
        });
    }
    let mut in_body = |callee: FnId, args: &[Ty], span: SpanId| f(callee, args, span, false);
    match &decl.body {
        Body::None => {}
        Body::Spec(e) | Body::Constant(e) => expr_calls(e, &mut in_body),
        Body::Stmts(block) => {
            for stmt in &block.stmts {
                stmt_calls(stmt, &mut in_body);
            }
        }
    }
}

fn stmt_calls(stmt: &Stmt, f: &mut dyn FnMut(FnId, &[Ty], SpanId)) {
    match &stmt.kind {
        StmtKind::BroadcastUse { callee } => f(*callee, &[], stmt.span),
        StmtKind::Let { init, .. } => {
            if let Some(init) = init {
                expr_calls(init, f);
            }
        }
        StmtKind::LetChecked { init, .. } => expr_calls(init, f),
        StmtKind::Assign { value, .. } | StmtKind::AssignSpec { value, .. } => expr_calls(value, f),
        StmtKind::Call {
            callee,
            type_args,
            args,
            ..
        } => {
            for arg in args {
                expr_calls(arg, f);
            }
            f(*callee, type_args, stmt.span);
        }
        StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => expr_calls(expr, f),
        StmtKind::AssertBitVector {
            requires, ensures, ..
        } => {
            for clause in requires.iter().chain(ensures) {
                expr_calls(&clause.expr, f);
            }
        }
        StmtKind::If {
            cond,
            then_block,
            else_block,
        }
        | StmtKind::IfSpec {
            cond,
            then_block,
            else_block,
        } => {
            expr_calls(cond, f);
            for s in then_block.stmts.iter().chain(&else_block.stmts) {
                stmt_calls(s, f);
            }
        }
        StmtKind::Return { value, .. } => {
            if let Some(value) = value {
                expr_calls(value, f);
            }
        }
        StmtKind::Loop(lp) => {
            if let Some(cond) = &lp.cond {
                expr_calls(&cond.expr, f);
                for s in &cond.block.stmts {
                    stmt_calls(s, f);
                }
            }
            for inv in &lp.invariants {
                expr_calls(&inv.expr, f);
            }
            for d in &lp.decreases {
                expr_calls(d, f);
            }
            for s in &lp.body.stmts {
                stmt_calls(s, f);
            }
        }
        StmtKind::Ghost(block) | StmtKind::Block(block) => {
            for s in &block.stmts {
                stmt_calls(s, f);
            }
        }
        StmtKind::GhostTail { block, tail } => {
            for statement in &block.stmts {
                stmt_calls(statement, f);
            }
            expr_calls(tail, f);
        }
        StmtKind::Reveal { .. }
        | StmtKind::BorrowMut { .. }
        | StmtKind::Hide { .. }
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Unreachable => {}
    }
}

fn expr_calls(e: &Expr, f: &mut dyn FnMut(FnId, &[Ty], SpanId)) {
    match &e.kind {
        ExprKind::Call {
            callee, type_args, ..
        } => f(*callee, type_args, e.span),
        ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
            for stmt in &block.stmts {
                stmt_calls(stmt, f);
            }
        }
        _ => {}
    }
    e.for_each_child(&mut |child| expr_calls(child, f));
}

/// Codegen selection requires a fully normalized key in this exact environment.
/// Region erasure alone does not normalize substituted associated projections.
/// An unsupported key is a missing graph obligation, never an absent dependency.
fn normalized_trait_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mty::TypingEnv<'tcx>,
    trait_ref: mty::TraitRef<'tcx>,
    origin: rustc_hir::def_id::DefId,
) -> Result<mty::TraitRef<'tcx>, Refusal> {
    let erased = tcx.erase_and_anonymize_regions(trait_ref);
    if erased.has_escaping_bound_vars() {
        return Err(Refusal::new(
            "trait-normalization",
            "a trait dependency with an escaping type or const binder",
            tcx.def_span(origin),
        ));
    }
    tcx.try_normalize_erasing_regions(typing_env, mty::Unnormalized::new(erased))
        .map_err(|problem| {
            Refusal::new(
                "trait-normalization",
                format!("cannot normalize the trait dependency '{erased}': {problem:?}"),
                tcx.def_span(origin),
            )
        })
}

/// The implementations of this crate that satisfy the bounds of `def_id`
/// at `args`, and the bounds of those implementations in turn
/// (`rust_to_vir_base.rs`, `get_impl_paths`), each with whether Verus's graph
/// has it too. `skip_self` names the trait whose `Self` bound a trait method
/// call resolves through, which is not a dependency of the call
/// (`remove_self_trait_bound`). Bounds that mention type parameters are
/// resolved as Verus does, with the bounds of `env` in scope; without `env`,
/// or when that fails, a bound on a type built from type parameters counts
/// every implementation of its trait (not Verus's).
pub(crate) fn bound_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    args: mty::GenericArgs<'tcx>,
    skip_self: Option<rustc_hir::def_id::DefId>,
    env: Option<rustc_hir::def_id::DefId>,
) -> Result<Vec<(LocalDefId, bool)>, Refusal> {
    let mono = mty::TypingEnv::fully_monomorphized();
    let mut work: Vec<(mty::Clause<'tcx>, bool)> = tcx
        .clauses_of(def_id)
        .instantiate(tcx, args)
        .clauses
        .into_iter()
        .map(|clause| (clause.skip_normalization(), true))
        .collect();
    let mut out: Vec<(LocalDefId, bool)> = Vec::new();
    let mut index = 0;
    while index < work.len() && index < MAX_BOUND_DEPENDENCIES {
        let (clause, top) = work[index];
        index += 1;
        let mty::ClauseKind::Trait(pred) = clause.kind().skip_binder() else {
            continue;
        };
        // The implementation a trait method call resolves through is not a
        // dependency of the call, but the bounds it needs in turn are.
        let self_bound =
            top && Some(pred.def_id()) == skip_self && args.types().next() == Some(pred.self_ty());
        let trait_ref = tcx.erase_and_anonymize_regions(pred.trait_ref);
        if trait_ref.has_escaping_bound_vars() {
            return Err(Refusal::new(
                "trait-normalization",
                "a trait dependency with an escaping type or const binder",
                tcx.def_span(def_id),
            ));
        }
        let typing_env = if trait_ref.has_param() {
            env.map(|env| mty::TypingEnv::non_body_analysis(tcx, env))
        } else {
            Some(mono)
        };
        let source = match typing_env {
            Some(typing_env) => {
                let normalized = normalized_trait_ref(tcx, typing_env, trait_ref, def_id)?;
                tcx.codegen_select_candidate(typing_env.as_query_input(normalized))
                    .ok()
            }
            None => None,
        };
        match source {
            Some(rustc_middle::traits::ImplSource::UserDefined(data)) => {
                if let Some(local) = data.impl_def_id.as_local() {
                    if !self_bound {
                        match out.iter_mut().find(|(d, _)| *d == local) {
                            Some(entry) => entry.1 = true,
                            None => out.push((local, true)),
                        }
                    }
                }
                for nested in tcx
                    .clauses_of(data.impl_def_id)
                    .instantiate(tcx, data.args)
                    .clauses
                {
                    let nested = (nested.skip_normalization(), false);
                    if !work.contains(&nested) {
                        work.push(nested);
                    }
                }
            }
            Some(_) => {}
            // A bound on a type parameter is the caller's; a bound on a type
            // built from type parameters may take any implementation of the
            // trait, all of which are dependencies.
            None if trait_ref.has_param()
                && !matches!(trait_ref.self_ty().kind(), mty::Param(_)) =>
            {
                for imp in tcx.all_impls(trait_ref.def_id) {
                    if let Some(local) = imp.as_local() {
                        if !self_bound && !out.iter().any(|(d, _)| *d == local) {
                            out.push((local, false));
                        }
                        // What those implementations need in turn, at their
                        // own parameters.
                        for (nested, _) in tcx.explicit_clauses_of(local).clauses {
                            let nested = (*nested, false);
                            if !work.contains(&nested) {
                                work.push(nested);
                            }
                        }
                    }
                }
            }
            None => {}
        }
    }
    if index < work.len() {
        return Err(Refusal::new(
            "trait-normalization",
            "the existing trait-dependency traversal bound was reached before completion",
            tcx.def_span(def_id),
        ));
    }
    Ok(out)
}

/// Whether the trait bounds of `def_id` at `args` hold, for a definition
/// they guard: `None` when each bound holds or is not decided here; the
/// definition's order where one does not hold. Verus states a bound on a
/// Verus trait at a type only through an implementation's
/// `Trait-Impl-Axiom` or the bounds of the function it checks, so a bound
/// that rustc meets with neither never holds there and the definition
/// stays hidden ([`DefOrder::Later`]). A bound rustc cannot decide, or one
/// on another trait, which Verus may not state as a guard, makes the order
/// [`DefOrder::Unknown`]. Bounds that mention type parameters are decided
/// with the bounds of `env` in scope, and not at all without `env`.
pub(crate) fn unmet_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    args: mty::GenericArgs<'tcx>,
    env: Option<rustc_hir::def_id::DefId>,
    loose: bool,
) -> Option<DefOrder> {
    let mut out: Option<DefOrder> = None;
    let mut note = |order: DefOrder| {
        out = Some(match (out, order) {
            (Some(DefOrder::Later), _) | (_, DefOrder::Later) => DefOrder::Later,
            _ => DefOrder::Unknown,
        });
    };
    for clause in tcx.clauses_of(def_id).instantiate(tcx, args).clauses {
        let clause = clause.skip_normalization();
        let mty::ClauseKind::Trait(pred) = clause.kind().skip_binder() else {
            continue;
        };
        let verus_trait = super::is_verus_trait(tcx, pred.def_id(), loose);
        if pred.polarity != mty::ClausePolarity::Positive {
            note(DefOrder::Unknown);
            continue;
        }
        let trait_ref = tcx.erase_and_anonymize_regions(pred.trait_ref);
        if trait_ref.has_escaping_bound_vars() {
            if verus_trait {
                note(DefOrder::Unknown);
            }
            continue;
        }
        let typing_env = if trait_ref.has_param() {
            match env {
                Some(env) => mty::TypingEnv::non_body_analysis(tcx, env),
                None => continue,
            }
        } else {
            mty::TypingEnv::fully_monomorphized()
        };
        let Ok(trait_ref) =
            tcx.try_normalize_erasing_regions(typing_env, mty::Unnormalized::new(trait_ref))
        else {
            note(DefOrder::Unknown);
            continue;
        };
        match tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref)) {
            Ok(_) => {}
            Err(rustc_middle::traits::CodegenObligationError::Unimplemented) if verus_trait => {
                note(DefOrder::Later);
            }
            Err(_) => note(DefOrder::Unknown),
        }
    }
    out
}

use rustc_middle::ty::TypeVisitableExt;

/// The function-shaped values (methods and constants) of implementation `imp`.
fn methods_of(tcx: TyCtxt<'_>, imp: LocalDefId) -> Vec<LocalDefId> {
    tcx.associated_items(imp)
        .in_definition_order()
        .filter(|item| {
            matches!(
                item.kind,
                mty::AssocKind::Fn { .. } | mty::AssocKind::Const { .. }
            )
        })
        .filter_map(|item| item.def_id.as_local())
        .collect()
}

/// The implementation of this crate that an instance of the default
/// method `method` at `args` inherits it through: the implementation rustc
/// selects for the trait reference, when it does not override `method`.
/// `None` when `method` is not a method of a trait, or no such
/// implementation is selected.
fn inheriting_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: LocalDefId,
    args: mty::GenericArgs<'tcx>,
) -> Result<Option<LocalDefId>, Refusal> {
    let Some(trait_id) = tcx.trait_of_assoc(method.to_def_id()) else {
        return Ok(None);
    };
    let args = tcx.erase_and_anonymize_regions(args);
    let trait_ref = mty::TraitRef::new(
        tcx,
        trait_id,
        args.iter().take(tcx.generics_of(trait_id).count()),
    );
    let typing_env = mty::TypingEnv::fully_monomorphized();
    let trait_ref = normalized_trait_ref(tcx, typing_env, trait_ref, method.to_def_id())?;
    let Ok(rustc_middle::traits::ImplSource::UserDefined(data)) =
        tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref))
    else {
        return Ok(None);
    };
    let Some(imp) = data.impl_def_id.as_local() else {
        return Ok(None);
    };
    let overridden = tcx
        .associated_items(imp)
        .in_definition_order()
        .any(|item| item.trait_item_def_id() == Some(method.to_def_id()));
    Ok((!overridden).then_some(imp))
}

/// Default methods and constant values of this crate's trait which the
/// implementation `imp` does not override.
pub(crate) fn inherited_defaults(tcx: TyCtxt<'_>, imp: LocalDefId) -> Vec<LocalDefId> {
    if tcx.def_kind(imp) != (DefKind::Impl { of_trait: true }) {
        return Vec::new();
    }
    let trait_id = tcx.impl_trait_id(imp);
    if !trait_id.is_local() {
        return Vec::new();
    }
    let overridden: std::collections::HashSet<rustc_hir::def_id::DefId> = tcx
        .associated_items(imp)
        .in_definition_order()
        .filter_map(|item| item.trait_item_def_id())
        .collect();
    tcx.associated_items(trait_id)
        .in_definition_order()
        .filter(|item| {
            matches!(
                item.kind,
                mty::AssocKind::Fn { .. } | mty::AssocKind::Const { .. }
            )
        })
        .filter(|item| item.defaultness(tcx).has_value())
        .filter(|item| !overridden.contains(&item.def_id))
        .filter_map(|item| item.def_id.as_local())
        .collect()
}

/// The number of type parameters of the trait `trait_id`, `Self` included.
fn type_param_count(tcx: TyCtxt<'_>, trait_id: LocalDefId) -> usize {
    tcx.generics_of(trait_id)
        .own_params
        .iter()
        .filter(|p| matches!(p.kind, mty::GenericParamDefKind::Type { .. }))
        .count()
}

/// A node of Verus's graph where the error for a cycle through a trait
/// looks for it: a node of the exact graph, or a node Verus puts on an edge
/// into or out of an implementation (`recursive_types.rs`,
/// `new_span_info_node`), which counts as a node of the cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum VNode {
    Real(Node),
    /// Between an implementation and its trait and the implementations its
    /// trait's bounds need (`add_trait_impl_to_graph`).
    ImplSpan(LocalDefId),
    /// Between a function and an implementation a call in it needs
    /// (`add_call_graph_edges`).
    CallSpan(Node, LocalDefId),
}

/// The exact graph in the order Verus builds its own (`context.rs`,
/// `GlobalCtx::new`), and its strongly connected components in the order
/// Verus's Tarjan search completes them (`scc.rs`), which decides the cycle
/// Verus reports.
struct Ordered {
    succ: HashMap<VNode, Vec<VNode>>,
    /// The function each function node stands for (a copy's default
    /// method).
    defs: HashMap<Node, LocalDefId>,
    /// Components in completion order, each in the order its nodes leave
    /// the search stack.
    sccs: Vec<Vec<VNode>>,
}

impl Ordered {
    #[allow(clippy::too_many_arguments)]
    fn new(
        tcx: TyCtxt<'_>,
        exact: &BTreeMap<Node, BTreeSet<Node>>,
        direct: &BTreeSet<(Node, Node)>,
        defs: &HashMap<FnId, LocalDefId>,
        krate: &VcCrate,
        order: &HashMap<LocalDefId, usize>,
        call_pos: &HashMap<(Node, Node), u32>,
        req_ens: &BTreeMap<(Node, Node), Vec<u64>>,
    ) -> Self {
        let index = |d: LocalDefId| u64::from(d.local_def_index.as_u32());
        let position = |d: LocalDefId| order.get(&d).map_or(u64::MAX, |p| *p as u64);
        let def_of = |n: Node| match n {
            Node::Fun(id) => defs.get(&id).copied(),
            Node::Copy(_, method) => Some(method),
            Node::Trait(_) | Node::Impl(_) => None,
        };
        // Where Verus reads a function's edges: every function in order,
        // its copies of default methods last.
        let processed = |n: Node| -> [u64; 3] {
            match n {
                Node::Copy(imp, method) => [6, index(imp), position(method)],
                _ => [5, def_of(n).map_or(u64::MAX, position), 0],
            }
        };
        // The trait a method implementing a trait method, or a copy,
        // depends on first.
        let own_trait = |n: Node| -> Option<LocalDefId> {
            let def = def_of(n)?;
            let parent = tcx.local_parent(def);
            match (n, tcx.def_kind(parent)) {
                (Node::Copy(..), _) => Some(parent),
                (_, DefKind::Impl { of_trait: true }) => tcx.impl_trait_id(parent).as_local(),
                _ => None,
            }
        };
        let mut succ: HashMap<VNode, Vec<(Vec<u64>, VNode)>> = HashMap::new();
        let mut push = |from: VNode, key: Vec<u64>, to: VNode| {
            let list = succ.entry(from).or_default();
            if !list.iter().any(|(_, t)| *t == to) {
                list.push((key, to));
            }
        };
        for (from, targets) in exact {
            for to in targets {
                // A path through `TraitReqEns`: right after the method's own
                // trait.
                if let Some(key) = req_ens.get(&(*from, *to)) {
                    let mut key = key.clone();
                    key.insert(0, 0);
                    key.insert(1, 1);
                    push(VNode::Real(*from), key, VNode::Real(*to));
                    continue;
                }
                let spanned = !direct.contains(&(*from, *to));
                match (*from, *to) {
                    (Node::Impl(imp), Node::Trait(_) | Node::Impl(_)) => {
                        push(VNode::Real(*from), vec![0], VNode::ImplSpan(imp));
                        let key = match to {
                            Node::Impl(dep) => vec![0, index(*dep)],
                            _ => vec![1],
                        };
                        push(VNode::ImplSpan(imp), key, VNode::Real(*to));
                    }
                    (Node::Fun(_) | Node::Copy(..), Node::Impl(dep)) if spanned => {
                        let span = VNode::CallSpan(*from, dep);
                        push(VNode::Real(*from), vec![2, 0, index(dep)], span);
                        push(span, vec![0], VNode::Real(*to));
                    }
                    (Node::Trait(_), Node::Trait(bound)) => {
                        push(VNode::Real(*from), vec![0, index(bound)], VNode::Real(*to));
                    }
                    (Node::Trait(_) | Node::Impl(_), _) => {
                        let key = match to {
                            Node::Copy(_, method) => vec![2, position(*method)],
                            _ => vec![1, def_of(*to).map_or(u64::MAX, position)],
                        };
                        push(VNode::Real(*from), key, VNode::Real(*to));
                    }
                    (_, Node::Trait(t)) => {
                        let key = if own_trait(*from) == Some(t) {
                            vec![0]
                        } else {
                            vec![1, index(t)]
                        };
                        push(VNode::Real(*from), key, VNode::Real(*to));
                    }
                    (_, Node::Impl(dep)) => {
                        push(VNode::Real(*from), vec![3, index(dep)], VNode::Real(*to));
                    }
                    _ => {
                        let at = call_pos.get(&(*from, *to)).copied().unwrap_or(u32::MAX);
                        push(
                            VNode::Real(*from),
                            vec![2, 1, u64::from(at)],
                            VNode::Real(*to),
                        );
                    }
                }
            }
        }
        // The order Verus adds the nodes in: traits with bounds on other
        // traits, functions without a body (copies last), spec functions,
        // implementations, then what reading the implementations and the
        // functions adds.
        let bounded: BTreeSet<Node> = exact
            .iter()
            .flat_map(|(from, to)| to.iter().map(move |t| (*from, *t)))
            .filter(|(from, to)| matches!((from, to), (Node::Trait(_), Node::Trait(_))))
            .flat_map(|(from, to)| [from, to])
            .collect();
        let mut trait_first: HashMap<LocalDefId, Vec<u64>> = HashMap::new();
        for (from, targets) in exact {
            for to in targets {
                let (t, at) = match (*from, *to) {
                    (Node::Impl(imp), Node::Trait(t)) => (t, vec![4, index(imp), 1]),
                    (Node::Trait(t), f) | (f, Node::Trait(t))
                        if matches!(f, Node::Fun(_) | Node::Copy(..)) =>
                    {
                        let mut key = processed(f).to_vec();
                        key.push(1);
                        (t, key)
                    }
                    _ => continue,
                };
                let first = trait_first.entry(t).or_insert_with(|| at.clone());
                if at < *first {
                    *first = at;
                }
            }
        }
        let node_key = |n: VNode| -> Vec<u64> {
            match n {
                VNode::Real(Node::Trait(t)) if bounded.contains(&Node::Trait(t)) => {
                    vec![0, index(t)]
                }
                VNode::Real(Node::Trait(t)) => trait_first
                    .get(&t)
                    .cloned()
                    .unwrap_or_else(|| vec![9, index(t)]),
                VNode::Real(Node::Copy(imp, method)) => vec![1, 1, index(imp), position(method)],
                VNode::Real(node @ Node::Fun(id)) => {
                    let decl = krate.fn_decl(id);
                    match (def_of(node), decl) {
                        (Some(def), Some(decl)) if matches!(decl.body, Body::None) => {
                            vec![1, 0, position(def)]
                        }
                        (Some(def), Some(decl)) if decl.mode == Mode::Spec => {
                            vec![2, position(def)]
                        }
                        (Some(def), _) => vec![5, position(def)],
                        (None, _) => vec![9, id.0.hi, id.0.lo],
                    }
                }
                VNode::Real(Node::Impl(imp)) => vec![3, index(imp)],
                VNode::ImplSpan(imp) => vec![4, index(imp), 0],
                VNode::CallSpan(from, dep) => {
                    let mut key = processed(from).to_vec();
                    key.extend([2, index(dep)]);
                    key
                }
            }
        };
        let mut nodes: Vec<VNode> = succ
            .iter()
            .flat_map(|(from, to)| std::iter::once(*from).chain(to.iter().map(|(_, t)| *t)))
            .collect();
        nodes.sort_by_key(|n| node_key(*n));
        nodes.dedup();
        let succ: HashMap<VNode, Vec<VNode>> = succ
            .into_iter()
            .map(|(from, mut to)| {
                to.sort_by(|a, b| a.0.cmp(&b.0));
                (from, to.into_iter().map(|(_, t)| t).collect())
            })
            .collect();
        let sccs = tarjan_in_order(&nodes, &succ);
        let defs = nodes
            .iter()
            .filter_map(|n| match n {
                VNode::Real(node) => Some((*node, def_of(*node)?)),
                _ => None,
            })
            .collect();
        Self { succ, defs, sccs }
    }

    /// Where the component holding each node comes among the components,
    /// in the order the search completes them.
    fn ranks(&self) -> HashMap<Node, usize> {
        let mut out = HashMap::new();
        for (rank, scc) in self.sccs.iter().enumerate() {
            for node in scc {
                if let VNode::Real(node) = node {
                    out.insert(*node, rank);
                }
            }
        }
        out
    }

    /// The first cycle Verus reports among `members`: the component Verus
    /// completes first that holds some of them and a node that is not a
    /// function (a trait, an implementation, a node on an edge), and in it
    /// the shortest cycle back to the first such node to leave the search
    /// stack (`check_traits`, `shortest_cycle_back_to_self`). Gives the
    /// component's place and the first function of the cycle, where Verus
    /// reports it (`scc_error`).
    fn first_cycle(&self, members: &BTreeSet<Node>) -> Option<(usize, Option<LocalDefId>)> {
        for (rank, scc) in self.sccs.iter().enumerate() {
            let ours = scc
                .iter()
                .any(|n| matches!(n, VNode::Real(node) if members.contains(node)));
            let cyclic = scc.len() > 1
                || self
                    .succ
                    .get(&scc[0])
                    .is_some_and(|next| next.contains(&scc[0]));
            if !ours || !cyclic {
                continue;
            }
            let Some(start) = scc
                .iter()
                .find(|n| !matches!(n, VNode::Real(Node::Fun(_) | Node::Copy(..))))
            else {
                continue;
            };
            let cycle = self.shortest_cycle(*start);
            let function = cycle.iter().find_map(|n| match n {
                VNode::Real(node @ (Node::Fun(_) | Node::Copy(..))) => {
                    Some(self.defs.get(node).copied())
                }
                _ => None,
            });
            return Some((rank, function.flatten()));
        }
        None
    }

    /// The first shortest cycle from `start` back to it, breadth first in
    /// edge order (`scc.rs`, `shortest_cycle_back_to_self`).
    fn shortest_cycle(&self, start: VNode) -> Vec<VNode> {
        let mut paths: Vec<Vec<VNode>> = vec![vec![start]];
        let mut reached: std::collections::HashSet<VNode> = std::collections::HashSet::new();
        reached.insert(start);
        while !paths.is_empty() {
            let mut next_paths = Vec::new();
            for path in paths {
                let last = *path.last().unwrap_or(&start);
                for next in self.succ.get(&last).into_iter().flatten() {
                    if *next == start {
                        return path;
                    }
                    if reached.insert(*next) {
                        let mut longer = path.clone();
                        longer.push(*next);
                        next_paths.push(longer);
                    }
                }
            }
            paths = next_paths;
        }
        vec![start]
    }
}

/// Push `v` on the search stack with the next index.
fn enter(
    v: VNode,
    index: &mut HashMap<VNode, usize>,
    low: &mut HashMap<VNode, usize>,
    stack: &mut Vec<VNode>,
    on_stack: &mut std::collections::HashSet<VNode>,
) {
    let i = index.len();
    index.insert(v, i);
    low.insert(v, i);
    stack.push(v);
    on_stack.insert(v);
}

/// Tarjan's strongly connected components as Verus's `scc.rs` computes
/// them: roots in the order of `nodes`, successors in their order; the
/// components in the order they complete, each in the order its nodes leave
/// the stack.
fn tarjan_in_order(nodes: &[VNode], succ: &HashMap<VNode, Vec<VNode>>) -> Vec<Vec<VNode>> {
    let mut index: HashMap<VNode, usize> = HashMap::new();
    let mut low: HashMap<VNode, usize> = HashMap::new();
    let mut on_stack: std::collections::HashSet<VNode> = std::collections::HashSet::new();
    let mut stack: Vec<VNode> = Vec::new();
    let mut out: Vec<Vec<VNode>> = Vec::new();
    let empty: Vec<VNode> = Vec::new();
    for root in nodes {
        if index.contains_key(root) {
            continue;
        }
        let mut frames: Vec<(VNode, usize)> = Vec::new();
        enter(*root, &mut index, &mut low, &mut stack, &mut on_stack);
        frames.push((*root, 0));
        while let Some((v, next)) = frames.last_mut() {
            let v = *v;
            let children = succ.get(&v).unwrap_or(&empty);
            if let Some(w) = children.get(*next) {
                *next += 1;
                let w = *w;
                if !index.contains_key(&w) {
                    enter(w, &mut index, &mut low, &mut stack, &mut on_stack);
                    frames.push((w, 0));
                } else if on_stack.contains(&w) {
                    let l = low[&v].min(index[&w]);
                    low.insert(v, l);
                }
                continue;
            }
            frames.pop();
            if let Some((u, _)) = frames.last() {
                let l = low[u].min(low[&v]);
                low.insert(*u, l);
            }
            if low[&v] == index[&v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack.remove(&w);
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                out.push(component);
            }
        }
    }
    out
}

/// The nodes reachable from `start` in `edges` (`start` only when it is on a
/// cycle).
fn reachable(edges: &BTreeMap<Node, BTreeSet<Node>>, start: Node) -> BTreeSet<Node> {
    let mut seen = BTreeSet::new();
    let mut work: Vec<Node> = edges.get(&start).into_iter().flatten().copied().collect();
    while let Some(node) = work.pop() {
        if seen.insert(node) {
            work.extend(edges.get(&node).into_iter().flatten().copied());
        }
    }
    seen
}

/// Tarjan's strongly connected components of `edges`, each a list of
/// nodes.
fn strongly_connected<N: Copy + Ord + std::hash::Hash>(
    edges: &BTreeMap<N, BTreeSet<N>>,
) -> Vec<Vec<N>> {
    struct State<'e, N> {
        edges: &'e BTreeMap<N, BTreeSet<N>>,
        index: HashMap<N, usize>,
        low: HashMap<N, usize>,
        on_stack: BTreeSet<N>,
        stack: Vec<N>,
        next: usize,
        out: Vec<Vec<N>>,
    }
    // Iterative to keep deep graphs off the call stack.
    fn visit<N: Copy + Ord + std::hash::Hash>(state: &mut State<'_, N>, root: N) {
        let mut frames: Vec<(N, Vec<N>)> = Vec::new();
        let enter = |state: &mut State<'_, N>, node: N| -> Vec<N> {
            state.index.insert(node, state.next);
            state.low.insert(node, state.next);
            state.next += 1;
            state.stack.push(node);
            state.on_stack.insert(node);
            state
                .edges
                .get(&node)
                .map(|n| n.iter().rev().copied().collect())
                .unwrap_or_default()
        };
        let children = enter(state, root);
        frames.push((root, children));
        while let Some((node, children)) = frames.last_mut() {
            let node = *node;
            if let Some(child) = children.pop() {
                if !state.index.contains_key(&child) {
                    let grand = enter(state, child);
                    frames.push((child, grand));
                } else if state.on_stack.contains(&child) {
                    let low = state.low[&node].min(state.index[&child]);
                    state.low.insert(node, low);
                }
                continue;
            }
            frames.pop();
            if let Some((parent, _)) = frames.last() {
                let low = state.low[parent].min(state.low[&node]);
                state.low.insert(*parent, low);
            }
            if state.low[&node] == state.index[&node] {
                let mut component = Vec::new();
                while let Some(top) = state.stack.pop() {
                    state.on_stack.remove(&top);
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                state.out.push(component);
            }
        }
    }
    let mut state = State {
        edges,
        index: HashMap::new(),
        low: HashMap::new(),
        on_stack: BTreeSet::new(),
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    let nodes: Vec<N> = edges
        .iter()
        .flat_map(|(from, to)| std::iter::once(*from).chain(to.iter().copied()))
        .collect();
    for node in nodes {
        if !state.index.contains_key(&node) {
            visit(&mut state, node);
        }
    }
    state.out
}
