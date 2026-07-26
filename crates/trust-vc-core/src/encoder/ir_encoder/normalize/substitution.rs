// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality substitution and binding back-propagation.
//! Extracted from monolithic normalize.rs as part of #2476.

use std::collections::HashMap;

use crate::ir_expr::{CompareOp, TrustVcExpr};

use super::arith::normalize_int_expr;

/// Extract an equality binding from an assumption expression.
///
/// Detects patterns like `var == expr` or `expr == var` and returns
/// `Some((var_name, rhs_expr))`. Only extracts simple `Var` on one side;
/// var-var equalities are skipped (no clear substitution direction).
pub(crate) fn extract_equality_binding(expr: &TrustVcExpr) -> Option<(String, TrustVcExpr)> {
    if let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = expr
    {
        // var == expr (non-var RHS)
        if let TrustVcExpr::Var { name, .. } = left.as_ref() {
            if !matches!(right.as_ref(), TrustVcExpr::Var { .. }) {
                return Some((name.clone(), *right.clone()));
            }
        }
        // expr == var (non-var LHS)
        if let TrustVcExpr::Var { name, .. } = right.as_ref() {
            if !matches!(left.as_ref(), TrustVcExpr::Var { .. }) {
                return Some((name.clone(), *left.clone()));
            }
        }
    }
    None
}

/// Substitute variables in a TrustVcExpr tree using provided bindings.
///
/// Replaces `Var { name }` nodes whose name appears in `bindings` with
/// the corresponding expression. Applied recursively.
pub(crate) fn substitute_vars(
    expr: &TrustVcExpr,
    bindings: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    if bindings.is_empty() {
        return expr.clone();
    }
    substitute_vars_inner(expr, bindings)
}

fn substitute_vars_inner(
    expr: &TrustVcExpr,
    bindings: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    match expr {
        TrustVcExpr::Var { name, .. } => {
            if let Some(replacement) = bindings.get(name) {
                replacement.clone()
            } else {
                expr.clone()
            }
        }

        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(substitute_vars_inner(left, bindings)),
            right: Box::new(substitute_vars_inner(right, bindings)),
            ty: ty.clone(),
        },

        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op: *op,
            left: Box::new(substitute_vars_inner(left, bindings)),
            right: Box::new(substitute_vars_inner(right, bindings)),
        },

        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op: *op,
            left: Box::new(substitute_vars_inner(left, bindings)),
            right: Box::new(substitute_vars_inner(right, bindings)),
        },

        TrustVcExpr::Not(inner) => {
            TrustVcExpr::Not(Box::new(substitute_vars_inner(inner, bindings)))
        }

        TrustVcExpr::Neg(inner) => {
            TrustVcExpr::Neg(Box::new(substitute_vars_inner(inner, bindings)))
        }

        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: Box::new(substitute_vars_inner(premise, bindings)),
            conclusion: Box::new(substitute_vars_inner(conclusion, bindings)),
        },

        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: Box::new(substitute_vars_inner(cond, bindings)),
            then_branch: Box::new(substitute_vars_inner(then_branch, bindings)),
            else_branch: Box::new(substitute_vars_inner(else_branch, bindings)),
            ty: ty.clone(),
        },

        // Leaf nodes and complex nodes (quantifiers, collections, etc.):
        // return as-is. Substitution into quantifier bodies would require
        // capture-avoidance; not needed for Path A arithmetic equalities.
        _ => expr.clone(),
    }
}

/// Substitute equality assumptions into an expression, then normalize.
///
/// This is the combined transform for assertion encoding: first replace
/// variables with their assumed values, then canonicalize the resulting
/// arithmetic. The combination turns `q * y` (given `y == d * q2`) into
/// `q * (d * q2)`, which normalization then canonicalizes to `((d * q) * q2)`.
pub(crate) fn substitute_and_normalize(
    expr: &TrustVcExpr,
    equality_bindings: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    if equality_bindings.is_empty() {
        return normalize_int_expr(expr);
    }
    let substituted = substitute_vars(expr, equality_bindings);
    normalize_int_expr(&substituted)
}

/// Insert a resolved equality binding and back-propagate through existing bindings.
///
/// Pure helper — no solver dependency. Inserts `var_name → resolved_rhs` into
/// `bindings`, then substitutes the new binding into all prior bindings' values
/// so chained equalities resolve transitively. Returns `true` if the binding
/// was inserted (new variable), `false` if the variable already existed (duplicate).
///
/// Shared by the SMT assumption path (`add_typed_assumption`) and compute mode
/// (`build_compute_bindings`). Part of #2454.
pub(crate) fn insert_and_back_propagate(
    bindings: &mut HashMap<String, TrustVcExpr>,
    var_name: String,
    resolved_rhs: TrustVcExpr,
) -> bool {
    use std::collections::hash_map::Entry;
    match bindings.entry(var_name.clone()) {
        Entry::Vacant(e) => {
            e.insert(resolved_rhs);
        }
        Entry::Occupied(_) => return false,
    }

    // Back-propagate: substitute the new binding into all existing
    // bindings' values so chained equalities resolve transitively.
    if bindings.len() > 1 {
        if let Some(new_val) = bindings.get(&var_name).cloned() {
            let one_binding = HashMap::from([(var_name.clone(), new_val)]);
            for (existing_var, existing_rhs) in bindings.iter_mut() {
                if *existing_var != var_name {
                    *existing_rhs = substitute_vars(existing_rhs, &one_binding);
                }
            }
        }
    }
    true
}

/// Accumulate an equality binding from an expression into a binding map.
///
/// Pure helper for compute mode — extracts `var == expr` from the expression,
/// resolves the RHS against existing bindings, inserts, and back-propagates.
/// Skips non-equality expressions and duplicate variables silently (fail-closed).
/// Part of #2454.
pub(crate) fn accumulate_equality_binding(
    expr: &TrustVcExpr,
    bindings: &mut HashMap<String, TrustVcExpr>,
) {
    let (var_name, rhs_expr) = match extract_equality_binding(expr) {
        Some(binding) => binding,
        None => return,
    };
    let resolved_rhs = if bindings.is_empty() {
        rhs_expr
    } else {
        substitute_vars(&rhs_expr, bindings)
    };
    insert_and_back_propagate(bindings, var_name, resolved_rhs);
}
