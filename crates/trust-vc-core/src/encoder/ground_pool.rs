//! Ground-term pool for bounded pre-solve broadcast/body-axiom chaining.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use ay_dpll::api::Term;

use super::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcExpr;

const GROUND_FIXPOINT_ROUNDS: usize = 1;

#[derive(Debug, Clone)]
pub(crate) struct GroundEntry {
    pub(crate) arg_terms: Vec<Term>,
    pub(crate) arg_exprs: Option<Vec<TrustVcExpr>>,
}

#[derive(Debug, Clone)]
pub(crate) struct GroundTrigger {
    pub(crate) symbol: String,
    pub(crate) arg_patterns: Vec<TrustVcExpr>,
    pub(crate) bound_exprs: Option<Vec<TrustVcExpr>>,
}

#[derive(Debug, Clone)]
pub(crate) struct GroundAxiom {
    pub(crate) name: String,
    pub(crate) seed_symbols: Vec<String>,
    pub(crate) seed_triggers: Vec<GroundTrigger>,
    pub(crate) bound_vars: Vec<String>,
    pub(crate) expr: TrustVcExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GroundKey {
    symbol: String,
    arg_terms: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AxiomInstanceKey {
    axiom_name: String,
    arg_terms: Vec<Term>,
}

#[derive(Debug, Clone)]
struct PendingGroundInstantiation {
    axiom: GroundAxiom,
    arg_terms: Vec<Term>,
    bound_exprs: Option<Vec<TrustVcExpr>>,
}

pub(crate) struct GroundTermPool {
    by_symbol: HashMap<String, Vec<GroundEntry>>,
    seen_entries: HashSet<GroundKey>,
    axioms: Vec<GroundAxiom>,
    instantiated_pairs: HashSet<AxiomInstanceKey>,
    revision: u64,
    last_flushed_revision: u64,
}

impl Default for GroundTermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl GroundTermPool {
    pub(crate) fn new() -> Self {
        Self {
            by_symbol: HashMap::new(),
            seen_entries: HashSet::new(),
            axioms: Vec::new(),
            instantiated_pairs: HashSet::new(),
            revision: 0,
            last_flushed_revision: 0,
        }
    }

    #[cfg(test)]
    pub(crate) fn register(&mut self, symbol: &str, arg_terms: Vec<Term>) -> bool {
        self.register_with_exprs(symbol, arg_terms, None)
    }

    pub(crate) fn register_expr(
        &mut self,
        symbol: &str,
        arg_terms: Vec<Term>,
        arg_exprs: Vec<TrustVcExpr>,
    ) -> bool {
        self.register_with_exprs(symbol, arg_terms, Some(arg_exprs))
    }

    fn register_with_exprs(
        &mut self,
        symbol: &str,
        arg_terms: Vec<Term>,
        arg_exprs: Option<Vec<TrustVcExpr>>,
    ) -> bool {
        let key = GroundKey {
            symbol: symbol.to_string(),
            arg_terms: arg_terms.clone(),
        };
        if !self.seen_entries.insert(key) {
            return false;
        }

        self.by_symbol
            .entry(symbol.to_string())
            .or_default()
            .push(GroundEntry {
                arg_terms,
                arg_exprs,
            });
        self.revision = self.revision.saturating_add(1);
        true
    }

    pub(crate) fn register_axiom(&mut self, mut axiom: GroundAxiom) {
        axiom.seed_symbols.sort();
        axiom.seed_symbols.dedup();
        if axiom.seed_symbols.is_empty() && axiom.seed_triggers.is_empty() {
            return;
        }
        self.axioms.push(axiom);
        self.revision = self.revision.saturating_add(1);
    }

    pub(crate) fn needs_flush(&self) -> bool {
        !self.axioms.is_empty() && self.revision != self.last_flushed_revision
    }

    /// Resets solver-dependent flush bookkeeping for encoder reuse after
    /// `try_pop()` retracts assertions that were flushed inside a push scope.
    ///
    /// After `try_pop()`, the solver no longer has the ground axiom instances
    /// that were asserted during the previous `flush_ground_axioms_to_fixpoint`
    /// call. Two pieces of state become stale:
    ///
    /// 1. `last_flushed_revision` — matches `revision`, so `needs_flush()`
    ///    returns false even though the solver no longer has the axioms.
    /// 2. `instantiated_pairs` — marks axiom+arg combinations as "already done",
    ///    preventing re-instantiation on subsequent assertions.
    ///
    /// This method clears both so the next `flush_ground_axioms_to_fixpoint`
    /// call re-emits all pending ground instances to the solver.
    ///
    /// Part of #2496.
    pub(crate) fn reset_flush_state(&mut self) {
        self.last_flushed_revision = 0;
        self.instantiated_pairs.clear();
    }

    fn revision(&self) -> u64 {
        self.revision
    }

    fn pending_instantiations(&self) -> Vec<PendingGroundInstantiation> {
        let mut pending = Vec::new();
        let mut seen_pending = HashSet::new();
        for axiom in &self.axioms {
            let trigger_symbols: HashSet<&str> = axiom
                .seed_triggers
                .iter()
                .map(|trigger| trigger.symbol.as_str())
                .collect();
            for trigger in &axiom.seed_triggers {
                let Some(entries) = self.by_symbol.get(&trigger.symbol) else {
                    continue;
                };
                for entry in entries {
                    if entry.arg_terms.len() != trigger.arg_patterns.len() {
                        continue;
                    }
                    let Some(arg_exprs) = entry.arg_exprs.as_deref() else {
                        continue;
                    };
                    let bound_exprs = if let Some(bound_exprs) = trigger.bound_exprs.clone() {
                        if !trigger_args_match(&trigger.arg_patterns, arg_exprs) {
                            continue;
                        }
                        bound_exprs
                    } else {
                        let Some(bound_exprs) =
                            match_trigger_args(&trigger.arg_patterns, arg_exprs, &axiom.bound_vars)
                        else {
                            continue;
                        };
                        bound_exprs
                    };
                    let key = AxiomInstanceKey {
                        axiom_name: axiom.name.clone(),
                        arg_terms: entry.arg_terms.clone(),
                    };
                    if self.instantiated_pairs.contains(&key) || !seen_pending.insert(key.clone()) {
                        continue;
                    }
                    pending.push(PendingGroundInstantiation {
                        axiom: axiom.clone(),
                        arg_terms: entry.arg_terms.clone(),
                        bound_exprs: Some(bound_exprs),
                    });
                }
            }

            for seed_symbol in &axiom.seed_symbols {
                if trigger_symbols.contains(seed_symbol.as_str()) {
                    continue;
                }
                let Some(entries) = self.by_symbol.get(seed_symbol) else {
                    continue;
                };
                for entry in entries {
                    if entry.arg_terms.len() != axiom.bound_vars.len() {
                        continue;
                    }
                    let key = AxiomInstanceKey {
                        axiom_name: axiom.name.clone(),
                        arg_terms: entry.arg_terms.clone(),
                    };
                    if self.instantiated_pairs.contains(&key) || !seen_pending.insert(key.clone()) {
                        continue;
                    }
                    pending.push(PendingGroundInstantiation {
                        axiom: axiom.clone(),
                        arg_terms: entry.arg_terms.clone(),
                        bound_exprs: None,
                    });
                }
            }
        }
        pending
    }

    fn mark_instantiated(&mut self, axiom_name: &str, arg_terms: Vec<Term>) {
        self.instantiated_pairs.insert(AxiomInstanceKey {
            axiom_name: axiom_name.to_string(),
            arg_terms,
        });
    }

    fn mark_flushed(&mut self) {
        self.last_flushed_revision = self.revision;
    }

    #[cfg(test)]
    pub(crate) fn ground_term_count(&self) -> usize {
        self.by_symbol.values().map(Vec::len).sum()
    }

    #[cfg(test)]
    pub(crate) fn revision_for_tests(&self) -> u64 {
        self.revision
    }

    #[cfg(test)]
    pub(crate) fn pending_instantiation_count_for_tests(&self) -> usize {
        self.pending_instantiations().len()
    }
}

fn trigger_args_match(patterns: &[TrustVcExpr], ground_args: &[TrustVcExpr]) -> bool {
    if patterns.len() != ground_args.len() {
        return false;
    }
    let empty_bound_vars = Vec::new();
    let mut bindings = HashMap::new();
    patterns.iter().zip(ground_args).all(|(pattern, ground)| {
        match_trigger_expr(pattern, ground, &empty_bound_vars, &mut bindings)
    })
}

/// Also reused by the interpreted-op dead-trigger broadcast ground replay
/// (`verification/broadcast.rs`) to match a single arithmetic trigger pattern
/// against candidate goal/assumption subexpressions at the IR level.
pub(crate) fn match_trigger_args(
    patterns: &[TrustVcExpr],
    ground_args: &[TrustVcExpr],
    bound_vars: &[String],
) -> Option<Vec<TrustVcExpr>> {
    if patterns.len() != ground_args.len() {
        return None;
    }

    let mut bindings: HashMap<&str, TrustVcExpr> = HashMap::new();
    for (pattern, ground) in patterns.iter().zip(ground_args) {
        if !match_trigger_expr(pattern, ground, bound_vars, &mut bindings) {
            return None;
        }
    }

    bound_vars
        .iter()
        .map(|name| bindings.get(name.as_str()).cloned())
        .collect()
}

fn match_trigger_expr<'a>(
    pattern: &'a TrustVcExpr,
    ground: &TrustVcExpr,
    bound_vars: &'a [String],
    bindings: &mut HashMap<&'a str, TrustVcExpr>,
) -> bool {
    if let TrustVcExpr::Var { name, .. } = pattern {
        if bound_vars.iter().any(|bound| bound == name) {
            return match bindings.get(name.as_str()) {
                Some(existing) => existing == ground,
                None => {
                    bindings.insert(name.as_str(), ground.clone());
                    true
                }
            };
        }
    }

    if pattern == ground {
        return true;
    }

    match (pattern, ground) {
        (
            TrustVcExpr::IntLit {
                value: pattern_value,
                ..
            },
            TrustVcExpr::IntLit {
                value: ground_value,
                ..
            },
        ) => pattern_value == ground_value,
        (
            TrustVcExpr::Arith {
                op: pattern_op,
                left: pattern_left,
                right: pattern_right,
                ..
            },
            TrustVcExpr::Arith {
                op: ground_op,
                left: ground_left,
                right: ground_right,
                ..
            },
        ) if pattern_op == ground_op => {
            match_trigger_expr(pattern_left, ground_left, bound_vars, bindings)
                && match_trigger_expr(pattern_right, ground_right, bound_vars, bindings)
        }
        (TrustVcExpr::Neg(pattern_inner), TrustVcExpr::Neg(ground_inner))
        | (TrustVcExpr::Not(pattern_inner), TrustVcExpr::Not(ground_inner)) => {
            match_trigger_expr(pattern_inner, ground_inner, bound_vars, bindings)
        }
        (
            TrustVcExpr::Cast {
                expr: pattern_expr,
                from_ty: pattern_from,
                to_ty: pattern_to,
            },
            TrustVcExpr::Cast {
                expr: ground_expr,
                from_ty: ground_from,
                to_ty: ground_to,
            },
        ) if pattern_from == ground_from && pattern_to == ground_to => {
            match_trigger_expr(pattern_expr, ground_expr, bound_vars, bindings)
        }
        (
            TrustVcExpr::FnCall {
                name: pattern_name,
                args: pattern_args,
                return_ty: pattern_return,
            },
            TrustVcExpr::FnCall {
                name: ground_name,
                args: ground_args,
                return_ty: ground_return,
            },
        ) if pattern_name == ground_name
            && pattern_return == ground_return
            && pattern_args.len() == ground_args.len() =>
        {
            pattern_args
                .iter()
                .zip(ground_args)
                .all(|(pattern_arg, ground_arg)| {
                    match_trigger_expr(pattern_arg, ground_arg, bound_vars, bindings)
                })
        }
        _ => false,
    }
}

impl AYEncoder {
    pub(crate) fn flush_ground_axioms_to_fixpoint(&mut self) -> TrustVcResult<usize> {
        if !self.state.ground_pool.needs_flush() {
            return Ok(0);
        }

        let mut total_instantiations = 0;
        let mut converged = false;

        for _ in 0..GROUND_FIXPOINT_ROUNDS {
            let round_start_revision = self.state.ground_pool.revision();
            let pending = self.state.ground_pool.pending_instantiations();
            if pending.is_empty() {
                converged = true;
                break;
            }

            for work in pending {
                let instance = if let Some(bound_exprs) = work.bound_exprs.as_ref() {
                    let substitutions: HashMap<&str, &TrustVcExpr> = work
                        .axiom
                        .bound_vars
                        .iter()
                        .map(String::as_str)
                        .zip(bound_exprs.iter())
                        .collect();
                    let substituted = crate::encoder::eval::substitute_vars_in_expr(
                        &work.axiom.expr,
                        &substitutions,
                    );
                    // Skip ground instances that capture a binder no longer in
                    // scope. A ground entry can be registered while a *transient*
                    // binder is live — e.g. an `assert_forall_by` universal
                    // variable `i`, declared only while verifying its own
                    // obligation, or carried into a later obligation's setup as a
                    // proven fact. By flush time (a different obligation, whose
                    // scope no longer declares that binder), re-encoding the
                    // substituted instance would fail with "undefined variable".
                    //
                    // Dropping such an instance is sound: it references a term
                    // (`f(i)` for the out-of-scope `i`) that does not occur in the
                    // current obligation's universe, so asserting it could neither
                    // discharge nor refute the in-scope goal. The flush re-encodes
                    // via `resolve_condition_typed`, which resolves free `Var`s
                    // solely through `self.variables` (no `local_vars`), so a free
                    // root name absent from `self.variables` is exactly the set of
                    // names `encode_var` would reject. This guard therefore fires
                    // *only* on the otherwise-erroring path and cannot regress any
                    // instance that previously encoded cleanly.
                    let captures_out_of_scope_binder =
                        crate::ir_expr_traversal::free_root_names(&substituted)
                            .iter()
                            .any(|name| !self.variables.contains_key(name));
                    if captures_out_of_scope_binder {
                        continue;
                    }
                    let normalized =
                        crate::encoder::ir_encoder::normalize::normalize_int_expr(&substituted);
                    crate::encoder::with_flag_unwind_safe!(
                        self.state.in_assumption_context,
                        true,
                        { self.resolve_condition_typed(&normalized) }
                    )
                    .map_err(|e| TrustVcError::Encoding {
                        context: "flush ground axioms",
                        detail: format!(
                            "Failed to encode ground instance for '{}': {}",
                            work.axiom.name, e
                        ),
                    })?
                } else {
                    let bindings: Vec<(&str, Term)> = work
                        .axiom
                        .bound_vars
                        .iter()
                        .map(String::as_str)
                        .zip(work.arg_terms.iter().copied())
                        .collect();
                    self.resolve_condition_typed_with_bindings(&work.axiom.expr, &bindings)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "flush ground axioms",
                            detail: format!(
                                "Failed to encode ground instance for '{}': {}",
                                work.axiom.name, e
                            ),
                        })?
                };
                self.solver
                    .try_assert_term(instance)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "flush ground axioms",
                        detail: format!(
                            "Failed to assert ground instance for '{}': {}",
                            work.axiom.name, e
                        ),
                    })?;
                self.state
                    .ground_pool
                    .mark_instantiated(&work.axiom.name, work.arg_terms);
                total_instantiations += 1;
            }

            if self.state.ground_pool.revision() == round_start_revision {
                converged = true;
                break;
            }
        }

        if converged {
            self.state.ground_pool.mark_flushed();
        }

        Ok(total_instantiations)
    }
}

#[cfg(test)]
#[path = "ground_pool_tests.rs"]
mod tests;
