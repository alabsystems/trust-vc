// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality substitution and binding back-propagation.
//! Extracted from monolithic normalize.rs as part of #2476.

use std::collections::HashMap;

use crate::ir::TrustVcType;
use crate::ir_expr::{CompareOp, TrustVcExpr};

use super::arith::normalize_int_expr;

/// Extract an equality binding from an assumption expression.
///
/// Detects patterns like `var == expr` or `expr == var` and returns
/// `Some((var_name, rhs_expr))`. Only extracts simple `Var` on one side;
/// var-var equalities are skipped (no clear substitution direction).
///
/// A float variable is never bound: IEEE `==` holds between `0.0` and `-0.0`,
/// which are different values (`1.0 / x` tells them apart), so `x == 0.0`
/// does not make `x` the value `0.0`. The equality is still asserted.
pub(crate) fn extract_equality_binding(expr: &TrustVcExpr) -> Option<(String, TrustVcExpr)> {
    if let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = expr
    {
        // var == expr (non-var RHS)
        if let TrustVcExpr::Var { name, ty } = left.as_ref() {
            if !matches!(right.as_ref(), TrustVcExpr::Var { .. }) {
                return (!is_float(ty)).then(|| (name.clone(), *right.clone()));
            }
        }
        // expr == var (non-var LHS)
        if let TrustVcExpr::Var { name, ty } = right.as_ref() {
            if !matches!(left.as_ref(), TrustVcExpr::Var { .. }) {
                return (!is_float(ty)).then(|| (name.clone(), *left.clone()));
            }
        }
    }
    None
}

fn is_float(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Float { .. })
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

/// The expression that may stand for a variable of type `var_ty` pinned to
/// `replacement`, or `None` when substituting would change what the variable
/// denotes (the variable is then kept; its equality is still asserted, so
/// nothing is lost but the rewrite).
///
/// For an integer-typed variable the replacement must BE a value of that type:
///
/// * an untyped literal form (`ir_lowering::is_untyped_literal`) is retyped to
///   the variable's type when every literal in it fits
///   (`ir_lowering::untyped_literal_at_peer`). For `i32` that retyping is the
///   identity — `i32` literals ARE the untyped placeholder — so the value is
///   pinned to `i32` by an identity cast instead. Substituted bare,
///   `x0: i32 == -128` made `-x0` the untyped `-(-128)`, which the `i8` peer
///   of `-x0 < z` then typed as the `i8` negation of `-128` (Verified, false),
///   and closed `x0 - x1` into an untyped tree a peer re-typed;
/// * any other replacement must have the variable's own (derived) type: an
///   expression of another type would retype every use of the variable.
///
/// Variables of every other type are substituted as before.
fn replacement_for(var_ty: &TrustVcType, replacement: &TrustVcExpr) -> Option<TrustVcExpr> {
    let integer_var = matches!(
        var_ty,
        TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::MathInt
            | TrustVcType::Nat
    );
    if !integer_var {
        return Some(replacement.clone());
    }
    if crate::ir_lowering::is_untyped_literal(replacement) {
        let typed = crate::ir_lowering::untyped_literal_at_peer(replacement, var_ty)?;
        if !matches!(var_ty, TrustVcType::Int { width: 32 }) {
            return Some(typed);
        }
        return Some(TrustVcExpr::Cast {
            expr: Box::new(typed),
            from_ty: var_ty.clone(),
            to_ty: var_ty.clone(),
        });
    }
    (crate::ir_lowering::infer_expr_type(replacement) == *var_ty).then(|| replacement.clone())
}

fn substitute_vars_inner(
    expr: &TrustVcExpr,
    bindings: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    match expr {
        TrustVcExpr::Var { name, ty } => bindings
            .get(name)
            .and_then(|replacement| replacement_for(ty, replacement))
            .unwrap_or_else(|| expr.clone()),

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
