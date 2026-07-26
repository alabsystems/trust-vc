//! Internal expression-depth limits for recursion hardening.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ir_expr::{MatchPattern, TrustVcExpr};

/// Internal hard stop for recursive expression processing.
///
/// Chosen to stay above the deepest committed supported verification shapes
/// while still fail-closing before pathological nesting can overflow the
/// default Rust test-thread stack during recursive IR encoding.
pub(crate) const MAX_EXPR_DEPTH: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("expression depth exceeds internal limit of {limit} during {stage}")]
pub(crate) struct ExprDepthError {
    pub(crate) limit: usize,
    pub(crate) stage: &'static str,
}

enum DepthItem<'a> {
    Expr(&'a TrustVcExpr, usize),
    Pattern(&'a MatchPattern, usize),
}

/// Iteratively validates that a `TrustVcExpr` stays within the internal depth
/// budget. This validator must remain iterative so it is safe on the same
/// pathological trees it rejects.
pub(crate) fn validate_expr_depth(
    expr: &TrustVcExpr,
    stage: &'static str,
) -> Result<(), ExprDepthError> {
    let mut stack = vec![DepthItem::Expr(expr, 1)];

    while let Some(item) = stack.pop() {
        match item {
            DepthItem::Expr(expr, depth) => {
                check_depth(depth, stage)?;
                let child_depth = depth + 1;
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
                        stack.push(DepthItem::Expr(right, child_depth));
                        stack.push(DepthItem::Expr(left, child_depth));
                    }
                    TrustVcExpr::Not(inner) | TrustVcExpr::Neg(inner) => {
                        stack.push(DepthItem::Expr(inner, child_depth));
                    }
                    TrustVcExpr::Implies {
                        premise,
                        conclusion,
                    } => {
                        stack.push(DepthItem::Expr(conclusion, child_depth));
                        stack.push(DepthItem::Expr(premise, child_depth));
                    }
                    TrustVcExpr::Ite {
                        cond,
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        stack.push(DepthItem::Expr(else_branch, child_depth));
                        stack.push(DepthItem::Expr(then_branch, child_depth));
                        stack.push(DepthItem::Expr(cond, child_depth));
                    }
                    TrustVcExpr::Let { value, body, .. } => {
                        stack.push(DepthItem::Expr(body, child_depth));
                        stack.push(DepthItem::Expr(value, child_depth));
                    }
                    TrustVcExpr::Cast { expr, .. } => {
                        stack.push(DepthItem::Expr(expr, child_depth));
                    }
                    TrustVcExpr::SpecClosure { body, .. } => {
                        stack.push(DepthItem::Expr(body, child_depth));
                    }
                    TrustVcExpr::CollectionOp { receiver, args, .. } => {
                        for arg in args.iter().rev() {
                            stack.push(DepthItem::Expr(arg, child_depth));
                        }
                        stack.push(DepthItem::Expr(receiver, child_depth));
                    }
                    TrustVcExpr::Index {
                        receiver, index, ..
                    } => {
                        stack.push(DepthItem::Expr(index, child_depth));
                        stack.push(DepthItem::Expr(receiver, child_depth));
                    }
                    TrustVcExpr::Quantifier { body, triggers, .. } => {
                        if let Some(trigger_groups) = triggers.as_ref() {
                            for group in trigger_groups.iter().rev() {
                                for trigger in group.iter().rev() {
                                    stack.push(DepthItem::Expr(trigger, child_depth));
                                }
                            }
                        }
                        stack.push(DepthItem::Expr(body, child_depth));
                    }
                    TrustVcExpr::FnCall { args, .. } => {
                        for arg in args.iter().rev() {
                            stack.push(DepthItem::Expr(arg, child_depth));
                        }
                    }
                    TrustVcExpr::Match {
                        scrutinee, arms, ..
                    } => {
                        for arm in arms.iter().rev() {
                            stack.push(DepthItem::Expr(&arm.body, child_depth));
                            stack.push(DepthItem::Pattern(&arm.pattern, child_depth));
                        }
                        stack.push(DepthItem::Expr(scrutinee, child_depth));
                    }
                    TrustVcExpr::Choose { condition, .. } => {
                        stack.push(DepthItem::Expr(condition, child_depth));
                    }
                    TrustVcExpr::ReadPlace { place, .. } => {
                        for proj in place.projections.iter().rev() {
                            if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                                stack.push(DepthItem::Expr(index, child_depth));
                            }
                        }
                    }
                    TrustVcExpr::PlaceDisjoint { left, right } => {
                        for place in [right, left] {
                            for proj in place.projections.iter().rev() {
                                if let crate::ir_place::PlaceProjection::Index { index, .. } = proj
                                {
                                    stack.push(DepthItem::Expr(index, child_depth));
                                }
                            }
                        }
                    }
                    TrustVcExpr::ProphecyNew { .. } => {}
                    TrustVcExpr::ProphecyResolve { value, .. } => {
                        stack.push(DepthItem::Expr(value, child_depth));
                    }
                }
            }
            DepthItem::Pattern(pattern, depth) => {
                check_depth(depth, stage)?;
                let child_depth = depth + 1;
                match pattern {
                    MatchPattern::Lit(expr) => stack.push(DepthItem::Expr(expr, child_depth)),
                    MatchPattern::Or(cases) => {
                        for case in cases.iter().rev() {
                            stack.push(DepthItem::Pattern(case, child_depth));
                        }
                    }
                    MatchPattern::Ident(_)
                    | MatchPattern::Struct { .. }
                    | MatchPattern::Constructor { .. }
                    | MatchPattern::Wildcard => {}
                }
            }
        }
    }

    Ok(())
}

fn check_depth(depth: usize, stage: &'static str) -> Result<(), ExprDepthError> {
    if depth > MAX_EXPR_DEPTH {
        Err(ExprDepthError {
            limit: MAX_EXPR_DEPTH,
            stage,
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
#[path = "expr_depth_tests.rs"]
mod tests;
