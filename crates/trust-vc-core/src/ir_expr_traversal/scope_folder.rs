//! Scope-aware owned-tree folder for `TrustVcExpr` trees with automatic
//! bound-name tracking.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Like [`ScopeAwareTrustVcExprVisitor`](super::ScopeAwareTrustVcExprVisitor) but
//! produces a new tree. Override `fold_expr_scoped` to transform specific nodes;
//! call `fold_expr_scoped_children` from within the override for structural
//! recursion with automatic scope management. Part of #2641.

use std::collections::HashSet;

use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

/// Scope-aware owned-tree folder for `TrustVcExpr` trees.
///
/// The `bound` parameter tracks all names bound by enclosing constructs.
pub(crate) trait ScopeAwareTrustVcExprFolder {
    fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
        fold_expr_scoped_children(self, expr, bound)
    }
}

/// Structural child-rebuild with automatic scope tracking for binding
/// constructs (Let, Quantifier, Match, Choose, SpecClosure).
///
/// At binding sites, bound variable names are added to `bound` before
/// recursing into the body (same semantics as `walk_expr_scoped_children`).
pub(crate) fn fold_expr_scoped_children<F: ScopeAwareTrustVcExprFolder + ?Sized>(
    f: &mut F,
    expr: TrustVcExpr,
    bound: &HashSet<&str>,
) -> TrustVcExpr {
    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => expr,

        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op,
            left: Box::new(f.fold_expr_scoped(*left, bound)),
            right: Box::new(f.fold_expr_scoped(*right, bound)),
            ty,
        },

        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(Box::new(f.fold_expr_scoped(*inner, bound))),

        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op,
            left: Box::new(f.fold_expr_scoped(*left, bound)),
            right: Box::new(f.fold_expr_scoped(*right, bound)),
        },

        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op,
            left: Box::new(f.fold_expr_scoped(*left, bound)),
            right: Box::new(f.fold_expr_scoped(*right, bound)),
        },

        TrustVcExpr::Not(inner) => TrustVcExpr::Not(Box::new(f.fold_expr_scoped(*inner, bound))),

        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: Box::new(f.fold_expr_scoped(*premise, bound)),
            conclusion: Box::new(f.fold_expr_scoped(*conclusion, bound)),
        },

        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: Box::new(f.fold_expr_scoped(*cond, bound)),
            then_branch: Box::new(f.fold_expr_scoped(*then_branch, bound)),
            else_branch: Box::new(f.fold_expr_scoped(*else_branch, bound)),
            ty,
        },

        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => TrustVcExpr::Cast {
            expr: Box::new(f.fold_expr_scoped(*expr, bound)),
            from_ty,
            to_ty,
        },

        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => TrustVcExpr::FnCall {
            name,
            args: args
                .into_iter()
                .map(|a| f.fold_expr_scoped(a, bound))
                .collect(),
            return_ty,
        },

        TrustVcExpr::CollectionOp {
            op,
            receiver,
            receiver_name,
            args,
            ty,
        } => TrustVcExpr::CollectionOp {
            op,
            receiver: Box::new(f.fold_expr_scoped(*receiver, bound)),
            receiver_name,
            args: args
                .into_iter()
                .map(|a| f.fold_expr_scoped(a, bound))
                .collect(),
            ty,
        },

        TrustVcExpr::Index {
            receiver,
            index,
            receiver_name,
            elem_ty,
        } => TrustVcExpr::Index {
            receiver: Box::new(f.fold_expr_scoped(*receiver, bound)),
            index: Box::new(f.fold_expr_scoped(*index, bound)),
            receiver_name,
            elem_ty,
        },

        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::SpecialArith {
            op,
            left: Box::new(f.fold_expr_scoped(*left, bound)),
            right: Box::new(f.fold_expr_scoped(*right, bound)),
            ty,
        },

        TrustVcExpr::WrappingArith {
            mode,
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::WrappingArith {
            mode,
            op,
            left: Box::new(f.fold_expr_scoped(*left, bound)),
            right: Box::new(f.fold_expr_scoped(*right, bound)),
            ty,
        },

        // --- Binding constructs: add bound names before recursing into body ---
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => {
            let new_value = Box::new(f.fold_expr_scoped(*value, bound));
            let new_body = {
                let mut inner = bound.clone();
                inner.insert(name.as_str());
                Box::new(f.fold_expr_scoped(*body, &inner))
            };
            TrustVcExpr::Let {
                name,
                ty,
                value: new_value,
                body: new_body,
            }
        }

        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => {
            let (new_body, new_triggers) = {
                let mut inner = bound.clone();
                for (bv_name, _) in &bound_vars {
                    inner.insert(bv_name.as_str());
                }
                let b = Box::new(f.fold_expr_scoped(*body, &inner));
                let t = triggers.map(|groups| {
                    groups
                        .into_iter()
                        .map(|group| {
                            group
                                .into_iter()
                                .map(|te| f.fold_expr_scoped(te, &inner))
                                .collect()
                        })
                        .collect()
                });
                (b, t)
            };
            TrustVcExpr::Quantifier {
                kind,
                bound_vars,
                body: new_body,
                triggers: new_triggers,
                trigger_inference_mode,
            }
        }

        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => {
            let new_scrutinee = Box::new(f.fold_expr_scoped(*scrutinee, bound));
            let new_arms = arms
                .into_iter()
                .map(|arm| {
                    let new_pattern = fold_match_pattern_scoped(f, arm.pattern, bound);
                    let names = crate::match_pattern_scope::pattern_bound_names(&new_pattern);
                    let mut inner = bound.clone();
                    for name in &names {
                        inner.insert(name.as_str());
                    }
                    MatchArm {
                        pattern: new_pattern,
                        // The guard references the arm's pattern bindings — fold it
                        // under the SAME inner scope as the body so capture-avoiding
                        // renaming reaches the guard's occurrences too.
                        guard: arm.guard.map(|g| f.fold_expr_scoped(g, &inner)),
                        body: f.fold_expr_scoped(arm.body, &inner),
                    }
                })
                .collect();
            TrustVcExpr::Match {
                scrutinee: new_scrutinee,
                arms: new_arms,
                ty,
            }
        }

        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            also_assert,
        } => {
            let new_condition = {
                let mut inner = bound.clone();
                inner.insert(var_name.as_str());
                Box::new(f.fold_expr_scoped(*condition, &inner))
            };
            // `also_assert` is a self-contained axiom (it binds its own
            // quantifier vars and references closed choices), so fold it under the
            // OUTER scope, not the choose binder.
            let new_also_assert = also_assert.map(|e| Box::new(f.fold_expr_scoped(*e, bound)));
            TrustVcExpr::Choose {
                var_name,
                var_ty,
                condition: new_condition,
                key,
                also_assert: new_also_assert,
            }
        }

        TrustVcExpr::SpecClosure { params, body, ty } => {
            let new_body = {
                let mut inner = bound.clone();
                for (param_name, _) in &params {
                    inner.insert(param_name.as_str());
                }
                Box::new(f.fold_expr_scoped(*body, &inner))
            };
            TrustVcExpr::SpecClosure {
                params,
                body: new_body,
                ty,
            }
        }

        // --- Place-based expressions: fold index projections ---
        TrustVcExpr::ReadPlace { place, ty } => TrustVcExpr::ReadPlace {
            place: fold_place_projections_scoped(f, place, bound),
            ty,
        },

        TrustVcExpr::PlaceDisjoint { left, right } => TrustVcExpr::PlaceDisjoint {
            left: fold_place_projections_scoped(f, left, bound),
            right: fold_place_projections_scoped(f, right, bound),
        },

        // --- Prophecy ---
        TrustVcExpr::ProphecyNew { name, ty } => TrustVcExpr::ProphecyNew { name, ty },

        TrustVcExpr::ProphecyResolve { name, value } => TrustVcExpr::ProphecyResolve {
            name,
            value: Box::new(f.fold_expr_scoped(*value, bound)),
        },
    }
}

/// Fold match pattern sub-expressions (Lit values, Or alternatives) through
/// the scoped folder. Patterns are folded in the outer scope (before bindings
/// are introduced).
fn fold_match_pattern_scoped<F: ScopeAwareTrustVcExprFolder + ?Sized>(
    f: &mut F,
    pattern: MatchPattern,
    bound: &HashSet<&str>,
) -> MatchPattern {
    match pattern {
        MatchPattern::Lit(expr) => MatchPattern::Lit(f.fold_expr_scoped(expr, bound)),
        MatchPattern::Or(patterns) => MatchPattern::Or(
            patterns
                .into_iter()
                .map(|p| fold_match_pattern_scoped(f, p, bound))
                .collect(),
        ),
        other => other,
    }
}

/// Fold index expressions in place projections through the scoped folder.
fn fold_place_projections_scoped<F: ScopeAwareTrustVcExprFolder + ?Sized>(
    f: &mut F,
    mut place: crate::ir_place::TrustVcPlace,
    bound: &HashSet<&str>,
) -> crate::ir_place::TrustVcPlace {
    place.projections = place
        .projections
        .into_iter()
        .map(|proj| match proj {
            crate::ir_place::PlaceProjection::Index { index, elem_ty } => {
                crate::ir_place::PlaceProjection::Index {
                    index: f.fold_expr_scoped(index, bound),
                    elem_ty,
                }
            }
            other => other,
        })
        .collect();
    place
}
