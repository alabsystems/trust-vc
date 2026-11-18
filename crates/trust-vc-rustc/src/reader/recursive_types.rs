//! Verus's check that every datatype has a base case
//! (`vir/src/recursive_types.rs`, `check_recursive_types`).
//!
//! A datatype is well founded when one of its variants has only fields whose
//! types are well founded: scalars, a type parameter (one that does not
//! accept recursive types; the reader refuses that attribute), a reference
//! or tuple of well-founded types, and a datatype that is well founded at
//! type arguments that are (`check_well_founded`, `check_well_founded_typ`).
//! A struct has one variant, so a struct that reaches itself through its
//! fields, through references, tuples or other structs, is not. Verus
//! computes the well-founded datatypes one strongly connected component of
//! the datatype graph at a time, in the order its graph sorts them, and
//! reports the first datatype of the first component that is left out:
//! "datatype must have at least one non-recursive variant", at the
//! datatype. It checks every datatype of the crate, used or not.
//!
//! The datatype graph (`build_datatype_graph`) has an edge from a datatype
//! to each datatype its bounds and fields mention, in the order a
//! post-order walk of their types meets them. Its nodes are numbered in the
//! order they are first met: each datatype in Verus's order
//! (`vir/src/ast_sort.rs`, `sort_krate`), then the datatypes its bounds and
//! fields mention. Tarjan's algorithm
//! (`vir/src/scc.rs`) completes the components in an order where a
//! component comes after every component it reaches, and lists the nodes of
//! one component in the order it pops them off its stack; that is the order
//! of the check.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self as mty, TyCtxt, TypeSuperVisitable, TypeVisitable, TypeVisitor};

use trust_vc_vcir::{AdtDecl, AdtId, Ty};

use super::{Cx, Refusal, UserError};

pub(super) enum DatatypeProblem {
    Cycle(UserError),
    Refused(Refusal),
}

/// The datatype Verus reports as having no non-recursive variant, if any.
/// `adts` are the crate's datatypes with their definitions, in Verus's
/// order.
pub(super) fn first_unfounded(
    cx: &Cx<'_>, adts: &[(LocalDefId, &AdtDecl)], all_adts: &[(LocalDefId, &AdtDecl)], items: &[LocalDefId],
) -> Result<Option<LocalDefId>, DatatypeProblem> {
    // Only this direct continuation uses A40's projection base-case rule.
    // Any unavailable dependency, exhausted traversal or actual cycle exits
    // before permissive foundedness; no summary flag is stored on Cx/IR.
    match super::cycles::associated_datatypes(cx, all_adts, items) {
        Ok(None) => {}
        Ok(Some(error)) => return Err(DatatypeProblem::Cycle(error)),
        Err(reason) => return Err(DatatypeProblem::Refused(reason)),
    }
    let founded = well_founded(adts.iter().map(|(_, decl)| *decl));
    let unfounded = adts
        .iter()
        .filter_map(|(_, decl)| (!founded.contains(&decl.id)).then_some(decl.id))
        .collect();
    Ok(first_unfounded_in(cx, adts, &unfounded))
}

/// Select a native primary from an independently validated failure set.
/// This only applies Verus's existing dependency-SCC ordering. It does not
/// recompute argument groundness or treat opaque foreign IDs as founded.
pub(super) fn first_unfounded_in(
    cx: &Cx<'_>,
    adts: &[(LocalDefId, &AdtDecl)],
    unfounded: &HashSet<AdtId>,
) -> Option<LocalDefId> {
    if !adts.iter().any(|(_, decl)| unfounded.contains(&decl.id)) {
        return None;
    }
    let def_of: HashMap<AdtId, LocalDefId> = adts
        .iter()
        .map(|(def_id, decl)| (decl.id, *def_id))
        .collect();
    let mut graph = Graph::default();
    for (def_id, decl) in adts {
        let node = graph.node(decl.id);
        for target in mentioned(cx, *def_id) {
            if def_of.contains_key(&target) {
                let target = graph.node(target);
                graph.edges[node].push(target);
            }
        }
    }
    graph
        .components()
        .into_iter()
        .flatten()
        .map(|node| graph.ids[node])
        .find(|id| unfounded.contains(id))
        .and_then(|id| def_of.get(&id).copied())
}

/// The well-founded datatypes among `adts`: the least set closed under
/// `check_well_founded`.
fn well_founded<'a>(adts: impl Iterator<Item = &'a AdtDecl> + Clone) -> HashSet<AdtId> {
    let mut founded = HashSet::new();
    loop {
        let before = founded.len();
        for decl in adts.clone() {
            if !founded.contains(&decl.id)
                && decl
                    .variants
                    .iter()
                    .any(|v| v.fields.iter().all(|f| ty_founded(&f.ty, &founded)))
            {
                founded.insert(decl.id);
            }
        }
        if founded.len() == before {
            return founded;
        }
    }
}

/// `check_well_founded_typ` on the types VcIR gives a field.
fn ty_founded(ty: &Ty, founded: &HashSet<AdtId>) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Unit | Ty::Param(_) => true,
        Ty::Tuple(elems) => elems.iter().all(|t| ty_founded(t, founded)),
        Ty::Ref { inner, .. } | Ty::MutRef(inner) => ty_founded(inner, founded),
        Ty::Adt(id, args) => founded.contains(id) && args.iter().all(|t| ty_founded(t, founded)),
        // A40 recursive_types.rs120-124: Reject-recursive base case. This
        // private traversal runs only after first_unfounded's actual raw
        // associated/selected-implementation graph completed successfully.
        Ty::Projection(..) => true,
    }
}

/// The datatypes of this crate that the bounds and then the fields of the
/// struct `def_id` mention, each time a post-order walk of their types
/// meets one (`WalkTypVisitorEnv` calls its function after the type's
/// parts).
fn mentioned(cx: &Cx<'_>, def_id: LocalDefId) -> Vec<AdtId> {
    let tcx = cx.tcx;
    let mut walk = Mentioned {
        cx,
        found: Vec::new(),
    };
    for (clause, _) in tcx.clauses_of(def_id).clauses {
        match clause.kind().skip_binder() {
            mty::ClauseKind::Trait(pred) => pred.trait_ref.args.visit_with(&mut walk),
            mty::ClauseKind::Projection(pred) => {
                pred.projection_term.args.visit_with(&mut walk);
                pred.term.visit_with(&mut walk);
            }
            _ => {}
        }
    }
    for field in tcx.adt_def(def_id).all_fields() {
        tcx.type_of(field.did)
            .instantiate_identity()
            .skip_normalization()
            .visit_with(&mut walk);
    }
    walk.found
}

struct Mentioned<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    found: Vec<AdtId>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for Mentioned<'_, 'tcx> {
    fn visit_ty(&mut self, ty: mty::Ty<'tcx>) {
        ty.super_visit_with(self);
        if let mty::Adt(adt, _) = ty.kind() {
            if let Some(id) = self.cx.adt_id(adt.did()) {
                self.found.push(id);
            }
        }
    }
}

/// The datatype graph, with `vir/src/scc.rs`'s numbering and search.
#[derive(Default)]
struct Graph {
    ids: Vec<AdtId>,
    index: HashMap<AdtId, usize>,
    edges: Vec<Vec<usize>>,
}

/// Tarjan's search state for one node.
#[derive(Clone, Copy)]
struct Visit {
    index: usize,
    lowlink: usize,
    on_stack: bool,
}

impl Graph {
    /// The node of `id`, added if new.
    fn node(&mut self, id: AdtId) -> usize {
        if let Some(node) = self.index.get(&id) {
            return *node;
        }
        let node = self.ids.len();
        self.ids.push(id);
        self.index.insert(id, node);
        self.edges.push(Vec::new());
        node
    }

    /// The strongly connected components in the order Tarjan's search
    /// completes them, each in the order its nodes leave the stack.
    fn components(&self) -> Vec<Vec<usize>> {
        let mut search = Search {
            graph: self,
            visits: vec![None; self.ids.len()],
            next: 0,
            stack: Vec::new(),
            components: Vec::new(),
        };
        for node in 0..self.ids.len() {
            if search.visits[node].is_none() {
                search.connect(node);
            }
        }
        search.components
    }
}

struct Search<'a> {
    graph: &'a Graph,
    visits: Vec<Option<Visit>>,
    next: usize,
    stack: Vec<usize>,
    components: Vec<Vec<usize>>,
}

impl Search<'_> {
    /// `strongconnect`.
    fn connect(&mut self, v: usize) {
        self.visits[v] = Some(Visit {
            index: self.next,
            lowlink: self.next,
            on_stack: true,
        });
        self.next += 1;
        self.stack.push(v);
        for &w in &self.graph.edges[v] {
            let low = match self.visits[w] {
                None => {
                    self.connect(w);
                    self.visit(w).lowlink
                }
                Some(seen) if seen.on_stack => seen.index,
                Some(_) => continue,
            };
            let visit = self.visit_mut(v);
            visit.lowlink = visit.lowlink.min(low);
        }
        let visit = self.visit(v);
        if visit.lowlink == visit.index {
            let mut component = Vec::new();
            while let Some(w) = self.stack.pop() {
                self.visit_mut(w).on_stack = false;
                component.push(w);
                if w == v {
                    break;
                }
            }
            self.components.push(component);
        }
    }

    fn visit(&self, node: usize) -> Visit {
        self.visits[node].expect("visited")
    }

    fn visit_mut(&mut self, node: usize) -> &mut Visit {
        self.visits[node].as_mut().expect("visited")
    }
}

#[cfg(test)]
mod tests {
    use super::Graph;
    use trust_vc_vcir::{AdtId, DefHash};

    fn id(n: u64) -> AdtId {
        AdtId(DefHash { hi: 0, lo: n })
    }

    fn graph(nodes: u64, edges: &[(u64, u64)]) -> Graph {
        let mut graph = Graph::default();
        for n in 0..nodes {
            graph.node(id(n));
        }
        for (a, b) in edges {
            let (a, b) = (graph.node(id(*a)), graph.node(id(*b)));
            graph.edges[a].push(b);
        }
        graph
    }

    #[test]
    fn unfounded_dependency_precedes_the_owner_that_reaches_it() {
        // Root { leaf: Leaf }, Leaf { next: Leaf }: both lack a base,
        // but the dependency component supplies Verus's first primary.
        let graph = graph(2, &[(0, 1), (1, 1)]);
        assert_eq!(graph.components(), vec![vec![1], vec![0]]);
    }

    #[test]
    fn components_complete_after_what_they_reach() {
        // 0 -> 1 -> 0, 0 -> 2: {2} completes first, then {0, 1} popped as
        // [1, 0].
        let g = graph(3, &[(0, 1), (1, 0), (0, 2)]);
        assert_eq!(g.components(), vec![vec![2], vec![1, 0]]);
    }

    #[test]
    fn unrelated_components_in_node_order() {
        let g = graph(3, &[(0, 0), (1, 1), (2, 2)]);
        assert_eq!(g.components(), vec![vec![0], vec![1], vec![2]]);
    }

    #[test]
    fn three_cycle_pops_in_reverse() {
        let g = graph(3, &[(0, 1), (1, 2), (2, 0)]);
        assert_eq!(g.components(), vec![vec![2, 1, 0]]);
    }
}
