//! Scope-aware visitor for `TrustVcExpr` trees with automatic bound-name
//! tracking.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Unlike the basic [`TrustVcExprVisitor`](super::TrustVcExprVisitor), this
//! variant automatically tracks bound variable names through binding constructs
//! (Let, Quantifier, Match, Choose, SpecClosure). Part of #2641.

use std::collections::HashSet;

use crate::ir_expr::TrustVcExpr;

/// Scope-aware visitor for `TrustVcExpr` trees.
///
/// The `bound` parameter contains all names bound by enclosing constructs at
/// each node. Return `true` from `visit_expr_scoped` to recurse into children,
/// `false` to skip (short-circuit).
pub(crate) trait ScopeAwareTrustVcExprVisitor {
    fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool;
}

/// Walk a `TrustVcExpr` tree with automatic scope tracking.
///
/// At each binding construct, the bound names are added to `bound`
/// before recursing into the body:
/// - Let: `name` added for body (not value)
/// - Quantifier: `bound_vars` added for body and triggers
/// - Match: pattern bindings added for arm body
/// - Choose: `var_name` added for condition
/// - SpecClosure: `params` added for body
pub(crate) fn walk_expr_scoped<V: ScopeAwareTrustVcExprVisitor>(
    v: &mut V,
    expr: &TrustVcExpr,
    bound: &HashSet<&str>,
) {
    if !v.visit_expr_scoped(expr, bound) {
        return;
    }
    walk_expr_scoped_children(v, expr, bound);
}

fn walk_expr_scoped_children<V: ScopeAwareTrustVcExprVisitor>(
    v: &mut V,
    expr: &TrustVcExpr,
    bound: &HashSet<&str>,
) {
    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => {}

        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            walk_expr_scoped(v, left, bound);
            walk_expr_scoped(v, right, bound);
        }

        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => {
            walk_expr_scoped(v, inner, bound);
        }

        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            walk_expr_scoped(v, premise, bound);
            walk_expr_scoped(v, conclusion, bound);
        }

        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            walk_expr_scoped(v, cond, bound);
            walk_expr_scoped(v, then_branch, bound);
            walk_expr_scoped(v, else_branch, bound);
        }

        TrustVcExpr::Cast { expr, .. } => {
            walk_expr_scoped(v, expr, bound);
        }

        TrustVcExpr::FnCall { args, .. } => {
            for arg in args {
                walk_expr_scoped(v, arg, bound);
            }
        }

        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            walk_expr_scoped(v, receiver, bound);
            for arg in args {
                walk_expr_scoped(v, arg, bound);
            }
        }

        TrustVcExpr::Index {
            receiver, index, ..
        } => {
            walk_expr_scoped(v, receiver, bound);
            walk_expr_scoped(v, index, bound);
        }

        TrustVcExpr::Let {
            name, value, body, ..
        } => {
            walk_expr_scoped(v, value, bound);
            let mut inner = bound.clone();
            inner.insert(name.as_str());
            walk_expr_scoped(v, body, &inner);
        }

        TrustVcExpr::Quantifier {
            bound_vars,
            body,
            triggers,
            ..
        } => {
            let mut inner = bound.clone();
            for (name, _) in bound_vars {
                inner.insert(name.as_str());
            }
            walk_expr_scoped(v, body, &inner);
            if let Some(groups) = triggers {
                for group in groups {
                    for t in group {
                        walk_expr_scoped(v, t, &inner);
                    }
                }
            }
        }

        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            walk_expr_scoped(v, scrutinee, bound);
            for arm in arms {
                let names = crate::match_pattern_scope::pattern_bound_names(&arm.pattern);
                let mut inner = bound.clone();
                for name in &names {
                    inner.insert(name.as_str());
                }
                // The guard references the arm's pattern bindings — walk it under the
                // same inner scope so a variable free ONLY in a guard is not dropped
                // (free-var collection drives Skolem-arg / CEGQI soundness).
                if let Some(guard) = &arm.guard {
                    walk_expr_scoped(v, guard, &inner);
                }
                walk_expr_scoped(v, &arm.body, &inner);
            }
        }

        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            let mut inner = bound.clone();
            inner.insert(var_name.as_str());
            walk_expr_scoped(v, condition, &inner);
        }

        TrustVcExpr::SpecClosure { params, body, .. } => {
            let mut inner = bound.clone();
            for (name, _) in params {
                inner.insert(name.as_str());
            }
            walk_expr_scoped(v, body, &inner);
        }

        TrustVcExpr::ReadPlace { place, .. } => {
            for proj in &place.projections {
                if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                    walk_expr_scoped(v, index, bound);
                }
            }
        }

        TrustVcExpr::PlaceDisjoint { left, right } => {
            for place in [left, right] {
                for proj in &place.projections {
                    if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                        walk_expr_scoped(v, index, bound);
                    }
                }
            }
        }

        TrustVcExpr::ProphecyNew { .. } => {}

        TrustVcExpr::ProphecyResolve { value, .. } => {
            walk_expr_scoped(v, value, bound);
        }
    }
}

fn push_free_root_name(
    free: &mut Vec<String>,
    seen: &mut HashSet<String>,
    bound: &HashSet<&str>,
    name: &str,
) {
    if !bound.contains(name) && seen.insert(name.to_string()) {
        free.push(name.to_string());
    }
}

/// Collect free root names from `expr`, respecting binding scopes.
///
/// Includes direct `Var` references, `ReadPlace` roots, and both roots of
/// `PlaceDisjoint`. Projection index expressions are visited recursively via
/// `walk_expr_scoped`.
pub(crate) fn free_root_names_with_initial_bound(
    expr: &TrustVcExpr,
    initial_bound: &HashSet<&str>,
) -> Vec<String> {
    struct Collector {
        free: Vec<String>,
        seen: HashSet<String>,
    }

    impl ScopeAwareTrustVcExprVisitor for Collector {
        fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool {
            match expr {
                TrustVcExpr::Var { name, .. } => {
                    push_free_root_name(&mut self.free, &mut self.seen, bound, name);
                }
                TrustVcExpr::ReadPlace { place, .. } => {
                    push_free_root_name(&mut self.free, &mut self.seen, bound, &place.root_name);
                }
                TrustVcExpr::PlaceDisjoint { left, right } => {
                    for place in [left, right] {
                        push_free_root_name(
                            &mut self.free,
                            &mut self.seen,
                            bound,
                            &place.root_name,
                        );
                    }
                }
                _ => {}
            }
            true
        }
    }

    let mut collector = Collector {
        free: Vec::new(),
        seen: HashSet::new(),
    };
    walk_expr_scoped(&mut collector, expr, initial_bound);
    collector.free
}

/// Collect free root names from `expr` as a set.
pub(crate) fn free_root_names(expr: &TrustVcExpr) -> HashSet<String> {
    free_root_names_with_initial_bound(expr, &HashSet::new())
        .into_iter()
        .collect()
}

/// Check if `expr` references any variable name in `names`, respecting
/// binding scopes (Let, Quantifier, Match, Choose, SpecClosure shadow
/// outer names).
///
/// Shared implementation replacing 3 independent copies in advanced.rs,
/// collection_seq/mod.rs, and trigger_inference/scope.rs. Part of #2641.
pub(crate) fn expr_references_any_name(expr: &TrustVcExpr, names: &HashSet<&str>) -> bool {
    struct Checker<'a> {
        names: &'a HashSet<&'a str>,
        found: bool,
    }
    impl ScopeAwareTrustVcExprVisitor for Checker<'_> {
        fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool {
            if self.found {
                return false;
            }
            if let TrustVcExpr::Var { name, .. } = expr {
                if self.names.contains(name.as_str()) && !bound.contains(name.as_str()) {
                    self.found = true;
                    return false;
                }
            }
            true
        }
    }
    let mut checker = Checker {
        names,
        found: false,
    };
    walk_expr_scoped(&mut checker, expr, &HashSet::new());
    checker.found
}
