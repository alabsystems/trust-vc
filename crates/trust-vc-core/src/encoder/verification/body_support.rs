//! Shared helpers for matching and extracting function body axioms.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::ir::TrustVcExpr;
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
use crate::prepared_context::PreparedObligation;

pub(super) const BODY_AXIOM_PREFIX: &str = "__body_axiom_";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ExtractedBodyAxiom {
    pub(super) function_name: String,
    pub(super) param_names: Vec<String>,
    /// Declared (possibly generic) parameter types, positionally aligned with
    /// `param_names`. Retained so a generic inline body can be monomorphized to
    /// the concrete instantiation implied by the call-site argument types
    /// (#2777, upstream inline.rs `inline_poly`): unifying each `param_type`
    /// against the actual argument type yields the `TypeParam`→concrete bindings.
    pub(super) param_types: Vec<crate::ir::TrustVcType>,
    pub(super) body: TrustVcExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DemandInlineSelection {
    pub(super) functions: Vec<String>,
    pub(super) depth_used: usize,
}

#[must_use]
pub(super) fn is_body_axiom(obligation: &PreparedObligation) -> bool {
    obligation.name.starts_with(BODY_AXIOM_PREFIX)
}

#[must_use]
pub(super) fn is_body_axiom_for_function(
    obligation: &PreparedObligation,
    function_name: &str,
) -> bool {
    if !is_body_axiom(obligation) {
        return false;
    }

    let suffix = &obligation.name[BODY_AXIOM_PREFIX.len()..];
    suffix == function_name
        || suffix.strip_prefix(function_name).is_some_and(|rest| {
            rest.starts_with('_') && rest[1..].chars().all(|c| c.is_ascii_digit())
        })
        || obligation
            .trigger_head_symbols()
            .into_iter()
            .any(|trigger_fn| trigger_fn.as_ref() == function_name)
}

/// Decides whether a body-axiom obligation's function is named in `fn_names`.
///
/// Shared matcher for BOTH per-query function-name sets that gate a defining
/// body axiom: the `reveal!` set (`ctx.revealed_fns`, which discloses an
/// opaque/hidden body) and the `hide!` set (`ctx.hidden_fns`, which suppresses
/// a non-opaque body). Matches in three ways, in order of specificity:
/// 1. the axiom-name suffix after `__body_axiom_` (encoder-test naming);
/// 2. any trigger head symbol verbatim (the bare-name in-crate `reveal!` path);
/// 3. the trailing `::`-segment (leaf) of a *qualified* trigger head symbol, so a
///    bare `reveal!(mul)` discloses a cross-crate dependency body axiom whose
///    trigger head is the fully-qualified `dep::module::mul`.
///
/// (3) only ever applies to qualified heads (`leaf != head`); a bare head's leaf
/// equals the head and is already covered by (2), so this is a strict superset
/// that leaves every existing bare-head opaque axiom unchanged. For the reveal
/// direction it is sound: a body axiom is a definitional equality
/// (`f(x..) == body`), always true, so revealing one can never make a false
/// goal provable. For the hide direction the same over-approximation is
/// fail-closed the other way: matching MORE axioms as hidden only suppresses
/// facts, which can never prove a goal Verus would reject. Part of #2778.
#[must_use]
pub(super) fn body_axiom_fn_named_in(
    obligation: &PreparedObligation,
    fn_names: &HashSet<String>,
) -> bool {
    // Robust to non-body-axiom names: unlike the original reveal-only matcher
    // (which was only ever called behind an `is_body_axiom` guard), this is
    // also consulted by the catalog builders on EVERY broadcast obligation —
    // a genuine `#[broadcast]` lemma's name has no `__body_axiom_` prefix, so
    // the name-suffix leg is skipped (never byte-sliced) for it.
    if let Some(axiom_fn_name) = obligation.name.strip_prefix(BODY_AXIOM_PREFIX) {
        if fn_names.contains(axiom_fn_name) {
            return true;
        }
    }
    obligation.trigger_head_symbols().into_iter().any(|head| {
        let head = head.as_ref();
        if fn_names.contains(head) {
            return true;
        }
        match head.rsplit_once("::") {
            Some((_, leaf)) => fn_names.contains(leaf),
            None => false,
        }
    })
}

/// Decides whether an opaque body-axiom obligation is revealed by `revealed_fns`.
/// Thin reveal-direction wrapper over [`body_axiom_fn_named_in`].
#[must_use]
pub(super) fn opaque_body_axiom_revealed(
    obligation: &PreparedObligation,
    revealed_fns: &HashSet<String>,
) -> bool {
    body_axiom_fn_named_in(obligation, revealed_fns)
}

/// Decides whether a bare function NAME (not an axiom obligation) is named in a
/// `reveal!`/`hide!` set, with the same qualified-leaf relaxation as
/// [`body_axiom_fn_named_in`]: a fully-qualified `dep::module::mul` matches a
/// bare `mul` entry. Used to strip hidden (unrevealed) functions out of the
/// call-site-substitution `inline_bodies` map so `hide!` also re-opaques
/// `#[inline]` spec functions (which have no live body axiom to suppress).
#[must_use]
pub(in crate::encoder) fn fn_name_named_in(name: &str, fn_names: &HashSet<String>) -> bool {
    if fn_names.contains(name) {
        return true;
    }
    match name.rsplit_once("::") {
        Some((_, leaf)) => fn_names.contains(leaf),
        None => false,
    }
}

#[must_use]
pub(super) fn extracted_body_axiom(obligation: &PreparedObligation) -> Option<ExtractedBodyAxiom> {
    is_body_axiom(obligation).then(|| extract_body_axiom(&obligation.expr))?
}

#[must_use]
pub(super) fn extracted_inline_body_axiom(
    obligation: &PreparedObligation,
) -> Option<ExtractedBodyAxiom> {
    obligation
        .is_inline
        .then(|| extracted_body_axiom(obligation))?
}

#[must_use]
pub(super) fn inline_body_axiom_extracted(obligation: &PreparedObligation) -> bool {
    extracted_inline_body_axiom(obligation).is_some()
}

/// Collects the names of all functions called in an expression tree.
/// Used by demand-inline retry to discover candidate callees. Part of #2655.
#[must_use]
pub(super) fn referenced_function_names(expr: &TrustVcExpr) -> HashSet<String> {
    struct V {
        names: HashSet<String>,
    }
    impl TrustVcExprVisitor for V {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if let TrustVcExpr::FnCall { name, .. } = expr {
                self.names.insert(name.clone());
            }
            walk_expr(self, expr);
        }
    }
    let mut v = V {
        names: HashSet::new(),
    };
    v.visit_expr(expr);
    v.names
}

/// Builds a body-axiom catalog from broadcast obligations. Maps function name
/// to the extracted body axiom for all visible bodies except direct
/// self-recursion. Mutually recursive bodies may enter so a termination-proven,
/// fully ground call can take an exact finite branch; Counterexample adoption is
/// separately guarded by [`selected_recursive_cycles_are_admitted`] and a
/// no-residual-call check in `assertion.rs`.
/// Used by demand-inline retry to find inlining candidates. Part of #2655.
///
/// Visibility is the user-controlled abstraction boundary and MUST agree with
/// the broadcast gate in `setup_broadcasts.rs`:
///   visible ⟺ (!is_opaque && !hidden) || revealed
/// An UNREVEALED opaque (`#[trust_vc::opaque]`) or hidden (`hide!`) body must
/// never enter the catalog — inlining it would let the demand-inline retry
/// prove (or refute) a goal from a body Verus keeps strictly uninterpreted,
/// the cardinal proves-more-than-Verus leak. A REVEALED body is inlinable:
/// `reveal!` makes the definitional equality available to the query, and
/// inlining an admitted definition is exact when expansion completes. On the
/// proc-macro path revealed-opaque axioms still carry
/// `is_opaque == true` (the reveal is query-level, not obligation-level), so
/// the reveal set must be consulted here rather than the flag alone.
#[must_use]
pub(super) fn build_body_catalog(
    broadcasts: &[&PreparedObligation],
    primary_fn: Option<&str>,
    revealed_fns: &HashSet<String>,
    hidden_fns: &HashSet<String>,
) -> std::collections::HashMap<String, ExtractedBodyAxiom> {
    let mut catalog = std::collections::HashMap::new();
    for broadcast in broadcasts {
        // Skip opaque/hidden bodies unless revealed — user-controlled
        // abstraction boundary (see doc-comment above).
        if (broadcast.is_opaque || body_axiom_fn_named_in(broadcast, hidden_fns))
            && !body_axiom_fn_named_in(broadcast, revealed_fns)
        {
            continue;
        }
        // Skip already-inline bodies — they're already substituted.
        if broadcast.is_inline {
            continue;
        }
        if let Some(body_axiom) = extracted_body_axiom(broadcast) {
            // Skip the primary function (self-recursion guard).
            if primary_fn.is_some_and(|pf| pf == body_axiom.function_name) {
                continue;
            }
            // Skip self-recursive bodies. Inlining a function whose body calls
            // itself never terminates — each expansion re-introduces the call —
            // so promoting it to inline would drive `substitute_inline_calls`
            // into unbounded recursion (stack overflow / SIGBUS). Verus and the
            // proc-macro inline path both reject recursive inline functions;
            // this enforces the same "non-recursive body axioms" contract the
            // catalog's doc-comment promises but previously did not check. A
            // recursive callee is still reasoned about via its defining
            // (broadcast) axiom and E-matching, not by inlining. Part of #54.
            if referenced_function_names(&body_axiom.body).contains(&body_axiom.function_name) {
                continue;
            }
            catalog.insert(body_axiom.function_name.clone(), body_axiom);
        }
    }
    catalog
}

/// Selects demand-inline candidates from the complete active query.
///
/// Calls in the failing assertion are considered first so a bounded retry
/// always prioritizes the goal. Calls in ordinary/scoped assumptions and
/// already-verified local facts are also direct (depth-one) roots: encoder
/// substitution applies to those expressions too, and leaving their redundant
/// quantified defining axioms live can make an otherwise-ground retry fail
/// model certification. Broadcast body axioms are deliberately not roots;
/// dependencies reachable from a selected body are discovered by the bounded
/// breadth-first expansion below. Part of #2655.
#[must_use]
pub(super) fn select_demand_inline_candidates(
    assertion_expr: &TrustVcExpr,
    supporting_exprs: &[&TrustVcExpr],
    catalog: &std::collections::HashMap<String, ExtractedBodyAxiom>,
    depth_bound: usize,
    max_callees: usize,
) -> DemandInlineSelection {
    if depth_bound == 0 || max_callees == 0 {
        return DemandInlineSelection {
            functions: Vec::new(),
            depth_used: 0,
        };
    }

    let mut selected: Vec<String> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    let mut depth_used = 0;

    // Depth 1: direct callees in the assertion first, then in supporting query
    // expressions. Sort within each root for deterministic selection while
    // preserving the caller-provided query priority.
    for root in std::iter::once(assertion_expr).chain(supporting_exprs.iter().copied()) {
        let mut direct_calls: Vec<String> = referenced_function_names(root).into_iter().collect();
        direct_calls.sort();
        for name in direct_calls {
            if selected.len() >= max_callees {
                break;
            }
            if catalog.contains_key(&name) && seen.insert(name.clone()) {
                selected.push(name);
                depth_used = 1;
            }
        }
        if selected.len() >= max_callees {
            break;
        }
    }

    // Depth 2+: breadth-first expansion through selected bodies.
    let mut frontier_start = 0;
    for depth in 2..=depth_bound {
        let frontier_end = selected.len();
        if frontier_start >= frontier_end {
            break;
        }
        let frontier: Vec<String> = selected[frontier_start..frontier_end].to_vec();
        frontier_start = frontier_end;

        for fn_name in &frontier {
            if selected.len() >= max_callees {
                break;
            }
            if let Some(body_axiom) = catalog.get(fn_name) {
                let mut body_calls: Vec<String> = referenced_function_names(&body_axiom.body)
                    .into_iter()
                    .collect();
                body_calls.sort();
                for callee in &body_calls {
                    if selected.len() >= max_callees {
                        break;
                    }
                    if catalog.contains_key(callee) && seen.insert(callee.clone()) {
                        selected.push(callee.clone());
                        depth_used = depth;
                    }
                }
            }
        }
    }

    DemandInlineSelection {
        functions: selected,
        depth_used,
    }
}

/// Checks the proof provenance needed to drop recursive defining axioms during
/// a demand-inline counterexample retry.
///
/// Acyclic candidates are exact macro expansion and need no extra authority.
/// Every member of a selected recursive SCC, however, must have been published
/// by the source catalog after its isolated termination proof succeeded.  The
/// set is carried as crate-private context metadata rather than inferred from an
/// obligation name, so an authored `__body_axiom_*` broadcast cannot forge it.
#[must_use]
pub(super) fn selected_recursive_cycles_are_admitted(
    catalog: &std::collections::HashMap<String, ExtractedBodyAxiom>,
    selected: &[String],
    admitted: &HashSet<String>,
) -> bool {
    let selected: HashSet<&str> = selected.iter().map(String::as_str).collect();
    for name in &selected {
        let forward = catalog_reachable_from(name, catalog);
        if !forward.contains(*name) {
            continue;
        }
        // Require authority for the whole SCC, not merely the goal-facing
        // member. A single unadmitted partner can make the global equation
        // system inconsistent even when the ground call chooses a base arm.
        for member in &forward {
            if catalog_reachable_from(member, catalog).contains(*name) && !admitted.contains(member)
            {
                return false;
            }
        }
    }
    true
}

fn catalog_reachable_from(
    start: &str,
    catalog: &std::collections::HashMap<String, ExtractedBodyAxiom>,
) -> HashSet<String> {
    let mut reached = HashSet::new();
    let Some(root) = catalog.get(start) else {
        return reached;
    };
    let mut pending: Vec<String> = referenced_function_names(&root.body)
        .into_iter()
        .filter(|name| catalog.contains_key(name))
        .collect();
    while let Some(name) = pending.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        if let Some(body) = catalog.get(&name) {
            pending.extend(
                referenced_function_names(&body.body)
                    .into_iter()
                    .filter(|callee| catalog.contains_key(callee)),
            );
        }
    }
    reached
}

fn extract_body_axiom(expr: &TrustVcExpr) -> Option<ExtractedBodyAxiom> {
    // A float definition is stated as `f(x) == body || (f(x) != f(x) && body
    // != body)`; substituting the body for the call is its exact reading.
    let (left, right) = crate::float_identity::identity_equation_sides(expr)?;
    let TrustVcExpr::FnCall { name, args, .. } = left else {
        return None;
    };
    // Capture each param's NAME and declared TYPE together: the body axiom's LHS
    // args are the formal params as `Var { name, ty }`, where `ty` is the
    // TEMPLATE param type (e.g. `Set(TypeParam("A"))`). The type is retained for
    // call-site monomorphization of a generic inline body.
    let params: Vec<(String, crate::ir::TrustVcType)> = args
        .iter()
        .map(|arg| match arg {
            TrustVcExpr::Var { name, ty } => Some((name.clone(), ty.clone())),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let (param_names, param_types) = params.into_iter().unzip();

    Some(ExtractedBodyAxiom {
        function_name: name.clone(),
        param_names,
        param_types,
        body: right.clone(),
    })
}

#[cfg(test)]
#[path = "body_support_tests.rs"]
mod tests;
