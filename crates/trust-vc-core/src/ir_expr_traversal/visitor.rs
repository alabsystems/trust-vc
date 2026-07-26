//! Shared-borrow visitor for `TrustVcExpr` trees.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Follows the `syn::visit` pattern: trait hooks with default implementations
//! that delegate to free `walk_*` helpers for child recursion. The exhaustive
//! match in `walk_expr` ensures new `TrustVcExpr` variants produce a compile
//! error until handled.
//!
//! Part of #2452.

use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

/// Shared-borrow visitor for `TrustVcExpr` trees.
///
/// Default implementations delegate to the corresponding `walk_*` function,
/// which recurses into all children. Override a hook to intercept specific
/// nodes; call `walk_*` from within the override to continue recursion.
pub(crate) trait TrustVcExprVisitor {
    fn visit_expr(&mut self, expr: &TrustVcExpr) {
        walk_expr(self, expr);
    }

    fn visit_match_arm(&mut self, arm: &MatchArm) {
        walk_match_arm(self, arm);
    }

    fn visit_match_pattern(&mut self, pattern: &MatchPattern) {
        walk_match_pattern(self, pattern);
    }
}

/// Exhaustive child-walk for `TrustVcExpr`. Visits all sub-expressions including
/// quantifier triggers, match arm bodies, and match pattern literals.
pub(crate) fn walk_expr<V: TrustVcExprVisitor + ?Sized>(v: &mut V, expr: &TrustVcExpr) {
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
            v.visit_expr(left);
            v.visit_expr(right);
        }

        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => {
            v.visit_expr(inner);
        }

        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            v.visit_expr(premise);
            v.visit_expr(conclusion);
        }

        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            v.visit_expr(cond);
            v.visit_expr(then_branch);
            v.visit_expr(else_branch);
        }

        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            v.visit_expr(scrutinee);
            for arm in arms {
                v.visit_match_arm(arm);
            }
        }

        TrustVcExpr::Let { value, body, .. } => {
            v.visit_expr(value);
            v.visit_expr(body);
        }

        TrustVcExpr::Cast { expr, .. } => {
            v.visit_expr(expr);
        }

        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            v.visit_expr(receiver);
            for arg in args {
                v.visit_expr(arg);
            }
        }

        TrustVcExpr::Index {
            receiver, index, ..
        } => {
            v.visit_expr(receiver);
            v.visit_expr(index);
        }

        TrustVcExpr::Quantifier { body, triggers, .. } => {
            v.visit_expr(body);
            if let Some(trigger_groups) = triggers {
                for group in trigger_groups {
                    for trigger in group {
                        v.visit_expr(trigger);
                    }
                }
            }
        }

        TrustVcExpr::FnCall { args, .. } => {
            for arg in args {
                v.visit_expr(arg);
            }
        }

        TrustVcExpr::SpecClosure { body, .. } => {
            v.visit_expr(body);
        }

        TrustVcExpr::Choose { condition, .. } => {
            v.visit_expr(condition);
        }

        TrustVcExpr::ReadPlace { place, .. } => {
            for proj in &place.projections {
                if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                    v.visit_expr(index);
                }
            }
        }

        TrustVcExpr::PlaceDisjoint { left, right } => {
            for place in [left, right] {
                for proj in &place.projections {
                    if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                        v.visit_expr(index);
                    }
                }
            }
        }

        TrustVcExpr::ProphecyNew { .. } => {}

        TrustVcExpr::ProphecyResolve { value, .. } => {
            v.visit_expr(value);
        }
    }
}

/// Walk a match arm: visit its pattern, then its guard (if any), then its body.
pub(crate) fn walk_match_arm<V: TrustVcExprVisitor + ?Sized>(v: &mut V, arm: &MatchArm) {
    v.visit_match_pattern(&arm.pattern);
    if let Some(guard) = &arm.guard {
        v.visit_expr(guard);
    }
    v.visit_expr(&arm.body);
}

/// Walk a match pattern: visit literal expressions and or-pattern children.
pub(crate) fn walk_match_pattern<V: TrustVcExprVisitor + ?Sized>(
    v: &mut V,
    pattern: &MatchPattern,
) {
    match pattern {
        MatchPattern::Lit(expr) => v.visit_expr(expr),
        MatchPattern::Ident(_)
        | MatchPattern::Wildcard
        | MatchPattern::Constructor { .. }
        | MatchPattern::Struct { .. } => {}
        MatchPattern::Or(patterns) => {
            for p in patterns {
                v.visit_match_pattern(p);
            }
        }
    }
}
