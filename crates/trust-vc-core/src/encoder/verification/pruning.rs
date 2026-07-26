//! SMT context pruning — remove unreachable declarations before solving.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Analyzes the reachability of function symbols from verification roots
//! (assertions, assumptions, invariants) and produces a prune plan that
//! `setup_from_prepared` uses to skip unreachable helpers and broadcasts.
//!
//! Part of #2520.

use std::collections::{HashMap, HashSet};

use super::VerificationSlices;
use crate::ir::{TraitDecl, TraitImplDecl, TrustVcExpr};
use crate::ir_expr_traversal::free_root_names;
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};

/// Result of reachability analysis: which functions are transitively
/// reachable from the verification roots through obligation expressions
/// and broadcast bodies.
#[derive(Debug)]
pub(super) struct CurrentStateSlice {
    /// Context variables still needed by the fresh per-assertion encoder.
    pub(super) reachable_variables: HashSet<String>,
    pub(super) selected_regular_assumptions: Vec<usize>,
    pub(super) selected_verified_invariants: Vec<usize>,
    pub(super) selected_verified_assert_by: Vec<usize>,
    pub(super) selected_scoped_assumptions: Vec<usize>,
}

/// Result of reachability analysis: which functions are transitively
/// reachable from the verification roots through obligation expressions
/// and broadcast bodies.
#[derive(Debug)]
pub(in crate::encoder) struct PrunePlan {
    /// Function names transitively reachable from the verification roots.
    pub(super) reachable_functions: HashSet<String>,
    /// Optional current-state variable/fact slice for fresh per-assertion
    /// encoders. Global/shared plans leave this as `None`.
    current_state_slice: Option<CurrentStateSlice>,
}

impl PrunePlan {
    /// Returns true if a broadcast's trigger heads intersect the reachable set,
    /// or if the broadcast is triggerless (always kept).
    pub(super) fn is_broadcast_reachable(&self, broadcast: &PreparedObligation) -> bool {
        let heads = broadcast.trigger_head_symbols();
        if heads.is_empty() {
            return true;
        }
        heads
            .iter()
            .any(|h| self.reachable_functions.contains(h.as_ref()))
    }

    /// Returns true if a helper function context is reachable.
    pub(super) fn is_helper_reachable(&self, name: &str) -> bool {
        self.reachable_functions.contains(name)
    }

    /// Returns true if any method UF for the trait is reachable from this query.
    pub(super) fn is_trait_reachable(&self, trait_decl: &TraitDecl) -> bool {
        trait_decl.methods.iter().any(|method| {
            self.reachable_functions
                .contains(&format!("{}__{}", trait_decl.name, method.name))
        })
    }

    /// Returns true if any trait method linked by this impl is reachable.
    pub(super) fn is_trait_impl_reachable(&self, impl_decl: &TraitImplDecl) -> bool {
        impl_decl.method_bindings.iter().any(|(trait_method, _)| {
            self.reachable_functions
                .contains(&format!("{}__{}", impl_decl.trait_name, trait_method))
        })
    }

    pub(super) fn current_state_slice(&self) -> Option<&CurrentStateSlice> {
        self.current_state_slice.as_ref()
    }
}

/// Collects function names referenced in `TrustVcExpr` trees.
struct FunctionCollector {
    functions: HashSet<String>,
}

impl TrustVcExprVisitor for FunctionCollector {
    fn visit_expr(&mut self, expr: &TrustVcExpr) {
        if let TrustVcExpr::FnCall { name, .. } = expr {
            self.functions.insert(name.clone());
        }
        walk_expr(self, expr);
    }
}

fn collect_functions_from_expr(expr: &TrustVcExpr) -> HashSet<String> {
    let mut collector = FunctionCollector {
        functions: HashSet::new(),
    };
    collector.visit_expr(expr);
    collector.functions
}

fn collect_fact_roots(obligation: &PreparedObligation) -> HashSet<String> {
    let mut roots = free_root_names(&obligation.expr);
    if let Some(ref guard) = obligation.broadcast_guard {
        roots.extend(free_root_names(guard));
    }
    roots
}

fn collect_lane_roots(obligations: &[&PreparedObligation]) -> Vec<HashSet<String>> {
    obligations
        .iter()
        .map(|obligation| collect_fact_roots(obligation))
        .collect()
}

fn select_lane(
    lane_roots: &[HashSet<String>],
    reachable_variables: &mut HashSet<String>,
    selected: &mut Vec<usize>,
) -> bool {
    let mut changed = false;
    for (index, roots) in lane_roots.iter().enumerate() {
        if selected.contains(&index) {
            continue;
        }
        if roots.is_empty() || !roots.is_disjoint(reachable_variables) {
            selected.push(index);
            let before = reachable_variables.len();
            reachable_variables.extend(roots.iter().cloned());
            changed |= reachable_variables.len() != before || !roots.is_empty();
        }
    }
    changed
}

/// Additional include path for the verified-`assert_by` lane: keep a PROVEN
/// QUANTIFIED `assert_by` fact when its collection/function-symbol footprint
/// intersects the obligation's footprint, even if the free-variable-root key
/// (`select_lane`) found nothing to latch onto.
///
/// Why this is needed: a quantified `assert_by` (`forall|i| pos2.contains(i) ==
/// (i > 0)`) is stored as its BARE body (`pos2.contains(i) == (i > 0)`); the
/// quantifier wrapper is reattached only at encode time (`setup.rs`). Its only
/// free root is the bound var `i`, which `free_root_names` excludes, and the
/// let-bound pure collection `pos2` is inlined to a memoized pure-constructor
/// term carrying no free `Var`/`ReadPlace` root. So a later BARE re-assert of
/// the same forall has EMPTY free roots and the root-intersection key drops the
/// proven fact. Relating on the shared collection/function symbols (`Set::new`,
/// the memoized `map`/`__set_map` head, `contains`) instead lets the proven
/// forall reach the re-assert's assumption set, where memoization makes it close
/// trivially.
///
/// SOUNDNESS: this only ever ADDS indices from `slices.verified_assert_by`, a
/// lane that by construction holds ONLY facts whose own obligation already
/// verified (`typed.rs` pushes an `assert_by` to this lane strictly after its
/// step returns `Verified`). Forwarding an already-discharged universal as a
/// quantified assumption to a LATER obligation is sound modus-ponens; widening
/// WHICH proven facts are visible can only expose true hypotheses and never
/// turns a genuine failure into a spurious pass. The gate to QUANTIFIED entries
/// keeps the wider key off scalar `assert_by` facts that the root key already
/// handles. Part of #2778.
fn select_quantified_assert_by_by_functions(
    slices: &VerificationSlices<'_>,
    assertion_functions: &HashSet<String>,
    reachable_variables: &mut HashSet<String>,
    selected: &mut Vec<usize>,
) -> bool {
    if assertion_functions.is_empty() {
        return false;
    }
    let mut changed = false;
    for (index, assert_by) in slices.verified_assert_by.iter().enumerate() {
        if selected.contains(&index) {
            continue;
        }
        // Gate strictly to QUANTIFIED, already-verified `assert_by` facts. A
        // non-empty `forall_bound_vars[name]` is exactly the condition under
        // which `setup.rs` reattaches the forall wrapper, i.e. the facts whose
        // bare-body roots cannot relate via `select_lane`.
        let is_quantified = slices
            .ctx
            .forall_bound_vars
            .get(&assert_by.name)
            .is_some_and(|bound_vars| !bound_vars.is_empty());
        if !is_quantified {
            continue;
        }
        let fact_functions = collect_functions_from_expr(&assert_by.expr);
        if fact_functions.is_disjoint(assertion_functions) {
            continue;
        }
        selected.push(index);
        reachable_variables.extend(collect_fact_roots(assert_by));
        changed = true;
    }
    changed
}

fn build_current_state_slice(
    assertion: &PreparedObligation,
    slices: &VerificationSlices<'_>,
    reachable_functions: &HashSet<String>,
) -> CurrentStateSlice {
    let mut reachable_variables = free_root_names(&assertion.expr);

    for broadcast in slices.broadcast_assumptions {
        let heads = broadcast.trigger_head_symbols();
        let broadcast_reachable = heads.is_empty()
            || heads
                .iter()
                .any(|head| reachable_functions.contains(head.as_ref()));
        if !broadcast_reachable {
            continue;
        }
        if let Some(bound_vars) = &broadcast.bound_vars {
            reachable_variables.extend(bound_vars.iter().cloned());
        }
        reachable_variables.extend(collect_fact_roots(broadcast));
    }

    let regular_roots = collect_lane_roots(slices.assumptions);
    let invariant_roots = collect_lane_roots(slices.verified_invariants);
    let assert_by_roots = collect_lane_roots(slices.verified_assert_by);
    let scoped_roots = collect_lane_roots(slices.scoped_assumptions);

    // Collection/function footprint of the obligation, used as the wider
    // relatedness key for quantified verified-`assert_by` facts whose only free
    // root is a quantifier-bound var (see
    // `select_quantified_assert_by_by_functions`).
    let assertion_functions = collect_functions_from_expr(&assertion.expr);

    let mut selected_regular_assumptions = Vec::new();
    let mut selected_verified_invariants = Vec::new();
    let mut selected_verified_assert_by = Vec::new();
    let mut selected_scoped_assumptions = Vec::new();

    loop {
        let mut changed = false;
        changed |= select_lane(
            &regular_roots,
            &mut reachable_variables,
            &mut selected_regular_assumptions,
        );
        changed |= select_lane(
            &invariant_roots,
            &mut reachable_variables,
            &mut selected_verified_invariants,
        );
        changed |= select_lane(
            &assert_by_roots,
            &mut reachable_variables,
            &mut selected_verified_assert_by,
        );
        changed |= select_quantified_assert_by_by_functions(
            slices,
            &assertion_functions,
            &mut reachable_variables,
            &mut selected_verified_assert_by,
        );
        changed |= select_lane(
            &scoped_roots,
            &mut reachable_variables,
            &mut selected_scoped_assumptions,
        );
        if !changed {
            break;
        }
    }

    selected_regular_assumptions.sort_unstable();
    selected_verified_invariants.sort_unstable();
    selected_verified_assert_by.sort_unstable();
    selected_scoped_assumptions.sort_unstable();

    CurrentStateSlice {
        reachable_variables,
        selected_regular_assumptions,
        selected_verified_invariants,
        selected_verified_assert_by,
        selected_scoped_assumptions,
    }
}

/// Expand reachability through broadcast bodies via trigger-head matching
/// until a fixed point. Shared worklist algorithm for both global and
/// per-assertion prune plans. Part of #2649.
#[allow(clippy::indexing_slicing)] // indices come from enumerate over broadcast_assumptions
fn expand_reachability(
    mut reachable: HashSet<String>,
    broadcast_assumptions: &[&PreparedObligation],
) -> PrunePlan {
    // Index broadcasts by trigger head for fixed-point expansion.
    let mut by_head: HashMap<String, Vec<usize>> = HashMap::new();
    let mut triggerless: Vec<usize> = Vec::new();
    for (i, broadcast) in broadcast_assumptions.iter().enumerate() {
        let heads = broadcast.trigger_head_symbols();
        if heads.is_empty() {
            triggerless.push(i);
        } else {
            for head in heads {
                by_head.entry(head.into_owned()).or_default().push(i);
            }
        }
    }

    // Fixed-point: expand reachability through broadcast bodies.
    // Always include functions discovered in triggerless broadcasts.
    let mut broadcast_visited = vec![false; broadcast_assumptions.len()];
    let mut worklist: Vec<String> = reachable.iter().cloned().collect();

    for &i in &triggerless {
        if !broadcast_visited[i] {
            broadcast_visited[i] = true;
            for f in collect_functions_from_expr(&broadcast_assumptions[i].expr) {
                if reachable.insert(f.clone()) {
                    worklist.push(f);
                }
            }
        }
    }

    while let Some(fn_name) = worklist.pop() {
        let indices: Vec<usize> = by_head.get(fn_name.as_str()).cloned().unwrap_or_default();
        for i in indices {
            if !broadcast_visited[i] {
                broadcast_visited[i] = true;
                for f in collect_functions_from_expr(&broadcast_assumptions[i].expr) {
                    if reachable.insert(f.clone()) {
                        worklist.push(f);
                    }
                }
            }
        }
    }

    PrunePlan {
        reachable_functions: reachable,
        current_state_slice: None,
    }
}

/// Seed reachable functions from trait impl bindings. Shared by both
/// global and per-assertion prune plans.
fn seed_trait_impl_bindings(reachable: &mut HashSet<String>, ctx: &PreparedVerificationContext) {
    for impl_decl in &ctx.trait_impl_decls {
        if impl_decl.concrete_type.contains_opaque() {
            continue;
        }
        for (_trait_method, concrete_fn) in &impl_decl.method_bindings {
            reachable.insert(concrete_fn.clone());
        }
    }
}

/// Build a prune plan by computing transitive function reachability.
///
/// Seeds from all obligations in the context and the primary function,
/// then expands through broadcast bodies via trigger-head matching until
/// a fixed point is reached.
///
/// This is a conservative over-approximation: the plan is built once from
/// ALL obligations, so any function mentioned by any obligation is reachable.
pub(in crate::encoder) fn build_prune_plan(
    ctx: &PreparedVerificationContext,
    broadcast_assumptions: &[&PreparedObligation],
) -> PrunePlan {
    let mut reachable: HashSet<String> = HashSet::new();
    if let Some(ref fc) = ctx.function_context {
        reachable.insert(fc.name.clone());
    }

    for ob in &ctx.obligations {
        reachable.extend(collect_functions_from_expr(&ob.expr));
    }

    for scope_obligations in ctx.assert_by_scopes.values() {
        for ob in scope_obligations {
            reachable.extend(collect_functions_from_expr(&ob.expr));
        }
    }

    seed_trait_impl_bindings(&mut reachable, ctx);
    expand_reachability(reachable, broadcast_assumptions)
}

/// Build a per-assertion prune plan seeded from a single assertion and its
/// active assumptions, producing a tighter reachable set than the global plan.
///
/// Used on the fresh-encoder path where each assertion gets its own encoder.
/// The shared-BV fast path keeps the global plan. Part of #2649.
pub(in crate::encoder) fn build_per_assertion_prune_plan(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
) -> PrunePlan {
    super::test_hooks::bump_per_assertion_prune_plan_build_count();
    let ctx = slices.ctx;
    let mut reachable: HashSet<String> = HashSet::new();

    // Seed 1: primary function (always needed for body axioms).
    if let Some(ref fc) = ctx.function_context {
        reachable.insert(fc.name.clone());
    }

    // Seed 2: the single assertion being verified.
    reachable.extend(collect_functions_from_expr(&assertion.expr));

    // Seed 3: active fact lanes (they constrain the context for this assertion).
    for assumption in slices.assumptions {
        reachable.extend(collect_functions_from_expr(&assumption.expr));
    }
    for invariant in slices.verified_invariants {
        reachable.extend(collect_functions_from_expr(&invariant.expr));
    }
    for assert_by in slices.verified_assert_by {
        reachable.extend(collect_functions_from_expr(&assert_by.expr));
    }
    for assumption in slices.scoped_assumptions {
        reachable.extend(collect_functions_from_expr(&assumption.expr));
    }

    // Seed 4: trait impl bindings (required for type linking axioms).
    seed_trait_impl_bindings(&mut reachable, ctx);

    let mut plan = expand_reachability(reachable, slices.broadcast_assumptions);
    plan.current_state_slice = Some(build_current_state_slice(
        assertion,
        slices,
        &plan.reachable_functions,
    ));
    plan
}

#[cfg(test)]
#[path = "pruning_audit_p582_tests.rs"]
mod pruning_audit_p582_tests;

#[cfg(test)]
#[path = "pruning_audit_tests.rs"]
mod pruning_audit_tests;

#[cfg(test)]
#[path = "pruning_tests.rs"]
mod tests;
