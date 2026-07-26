//! Owned-tree folder for `TrustVcExpr` trees.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Follows the `syn::fold` pattern: trait hooks with default implementations
//! that delegate to free `fold_*` helpers for child recursion. The exhaustive
//! match in `fold_expr_children` ensures new `TrustVcExpr` variants produce a
//! compile error until handled.
//!
//! Part of #2452.

use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

/// Owned-tree folder for `TrustVcExpr` trees.
///
/// Default implementations delegate to the corresponding `fold_*_children`
/// function, which recursively rebuilds all children. Override a hook to
/// transform specific nodes; call `fold_expr_children` from within the override
/// to continue the default rebuild.
pub(crate) trait TrustVcExprFolder {
    fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
        fold_expr_children(self, expr)
    }

    fn fold_match_arm(&mut self, arm: MatchArm) -> MatchArm {
        fold_match_arm_children(self, arm)
    }

    fn fold_match_pattern(&mut self, pattern: MatchPattern) -> MatchPattern {
        fold_match_pattern_children(self, pattern)
    }
}

/// Fold a boxed expression through the folder.
pub(crate) fn fold_boxed_expr<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    expr: Box<TrustVcExpr>,
) -> Box<TrustVcExpr> {
    Box::new(f.fold_expr(*expr))
}

/// Fold a vector of expressions through the folder.
pub(crate) fn fold_expr_vec<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    exprs: Vec<TrustVcExpr>,
) -> Vec<TrustVcExpr> {
    exprs.into_iter().map(|e| f.fold_expr(e)).collect()
}

/// Fold trigger groups (Vec<Vec<TrustVcExpr>>) through the folder.
pub(crate) fn fold_trigger_groups<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    groups: Vec<Vec<TrustVcExpr>>,
) -> Vec<Vec<TrustVcExpr>> {
    groups
        .into_iter()
        .map(|group| fold_expr_vec(f, group))
        .collect()
}

/// Exhaustive child-rebuild for `TrustVcExpr`. Rebuilds all children through the
/// folder, including quantifier triggers, match arm bodies, and match patterns.
pub(crate) fn fold_expr_children<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    expr: TrustVcExpr,
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
            left: fold_boxed_expr(f, left),
            right: fold_boxed_expr(f, right),
            ty,
        },

        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(fold_boxed_expr(f, inner)),

        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op,
            left: fold_boxed_expr(f, left),
            right: fold_boxed_expr(f, right),
        },

        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op,
            left: fold_boxed_expr(f, left),
            right: fold_boxed_expr(f, right),
        },

        TrustVcExpr::Not(inner) => TrustVcExpr::Not(fold_boxed_expr(f, inner)),

        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: fold_boxed_expr(f, premise),
            conclusion: fold_boxed_expr(f, conclusion),
        },

        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: fold_boxed_expr(f, cond),
            then_branch: fold_boxed_expr(f, then_branch),
            else_branch: fold_boxed_expr(f, else_branch),
            ty,
        },

        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => TrustVcExpr::Match {
            scrutinee: fold_boxed_expr(f, scrutinee),
            arms: arms.into_iter().map(|arm| f.fold_match_arm(arm)).collect(),
            ty,
        },

        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => TrustVcExpr::Let {
            name,
            ty,
            value: fold_boxed_expr(f, value),
            body: fold_boxed_expr(f, body),
        },

        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => TrustVcExpr::Cast {
            expr: fold_boxed_expr(f, expr),
            from_ty,
            to_ty,
        },

        TrustVcExpr::CollectionOp {
            op,
            receiver,
            receiver_name,
            args,
            ty,
        } => TrustVcExpr::CollectionOp {
            op,
            receiver: fold_boxed_expr(f, receiver),
            receiver_name,
            args: fold_expr_vec(f, args),
            ty,
        },

        TrustVcExpr::Index {
            receiver,
            index,
            receiver_name,
            elem_ty,
        } => TrustVcExpr::Index {
            receiver: fold_boxed_expr(f, receiver),
            index: fold_boxed_expr(f, index),
            receiver_name,
            elem_ty,
        },

        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body: fold_boxed_expr(f, body),
            triggers: triggers.map(|groups| fold_trigger_groups(f, groups)),
            trigger_inference_mode,
        },

        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => TrustVcExpr::FnCall {
            name,
            args: fold_expr_vec(f, args),
            return_ty,
        },

        TrustVcExpr::SpecClosure { params, body, ty } => TrustVcExpr::SpecClosure {
            params,
            body: fold_boxed_expr(f, body),
            ty,
        },

        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::SpecialArith {
            op,
            left: fold_boxed_expr(f, left),
            right: fold_boxed_expr(f, right),
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
            left: fold_boxed_expr(f, left),
            right: fold_boxed_expr(f, right),
            ty,
        },

        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            also_assert,
        } => TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition: fold_boxed_expr(f, condition),
            key,
            also_assert: also_assert.map(|e| fold_boxed_expr(f, e)),
        },

        TrustVcExpr::ReadPlace { place, ty } => {
            let folded_place = fold_place_projections(f, place);
            TrustVcExpr::ReadPlace {
                place: folded_place,
                ty,
            }
        }

        TrustVcExpr::PlaceDisjoint { left, right } => TrustVcExpr::PlaceDisjoint {
            left: fold_place_projections(f, left),
            right: fold_place_projections(f, right),
        },

        TrustVcExpr::ProphecyNew { name, ty } => TrustVcExpr::ProphecyNew { name, ty },

        TrustVcExpr::ProphecyResolve { name, value } => TrustVcExpr::ProphecyResolve {
            name,
            value: fold_boxed_expr(f, value),
        },
    }
}

/// Fold index expressions inside place projections through the folder.
pub(crate) fn fold_place_projections<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    mut place: crate::ir_place::TrustVcPlace,
) -> crate::ir_place::TrustVcPlace {
    place.projections = place
        .projections
        .into_iter()
        .map(|proj| match proj {
            crate::ir_place::PlaceProjection::Index { index, elem_ty } => {
                crate::ir_place::PlaceProjection::Index {
                    index: f.fold_expr(index),
                    elem_ty,
                }
            }
            other => other,
        })
        .collect();
    place
}

/// Rebuild a match arm's children through the folder.
pub(crate) fn fold_match_arm_children<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    arm: MatchArm,
) -> MatchArm {
    MatchArm {
        pattern: f.fold_match_pattern(arm.pattern),
        body: f.fold_expr(arm.body),
        // The guard is a child expression over the arm's pattern bindings — fold it
        // too, or a rewrite (substitution/inline) would silently drop it, turning a
        // guarded arm into an unconditional one (false-verify).
        guard: arm.guard.map(|g| f.fold_expr(g)),
    }
}

/// Rebuild a match pattern's children through the folder.
pub(crate) fn fold_match_pattern_children<F: TrustVcExprFolder + ?Sized>(
    f: &mut F,
    pattern: MatchPattern,
) -> MatchPattern {
    match pattern {
        MatchPattern::Lit(expr) => MatchPattern::Lit(f.fold_expr(expr)),
        MatchPattern::Or(patterns) => MatchPattern::Or(
            patterns
                .into_iter()
                .map(|p| f.fold_match_pattern(p))
                .collect(),
        ),
        other @ (MatchPattern::Ident(_)
        | MatchPattern::Wildcard
        | MatchPattern::Constructor { .. }
        | MatchPattern::Struct { .. }) => other,
    }
}
