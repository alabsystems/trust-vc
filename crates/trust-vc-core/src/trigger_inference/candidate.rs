// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use crate::ir_expr::TrustVcExpr;

use super::scope::{expr_references_any_bound, referenced_bound_vars};

/// A trigger candidate paired with the bound vars it genuinely covers,
/// accounting for variable shadowing at the point of collection.
pub(super) struct ScopedCandidate<'a> {
    pub(super) expr: TrustVcExpr,
    pub(super) covered: HashSet<&'a str>,
}

pub(super) fn collect_candidates<'a>(
    body: &TrustVcExpr,
    bound_names: &HashSet<&'a str>,
) -> Vec<ScopedCandidate<'a>> {
    let mut candidates = Vec::new();
    collect_candidates_inner(body, bound_names, &mut candidates);
    candidates
}

fn collect_candidates_inner<'a>(
    expr: &TrustVcExpr,
    bound_names: &HashSet<&'a str>,
    out: &mut Vec<ScopedCandidate<'a>>,
) {
    match expr {
        // Eligible: function call that references bound vars
        TrustVcExpr::FnCall { args, .. } => {
            if args
                .iter()
                .any(|a| expr_references_any_bound(a, bound_names))
            {
                let covered = referenced_bound_vars(expr, bound_names);
                out.push(ScopedCandidate {
                    expr: expr.clone(),
                    covered,
                });
            }
            // Also recurse into arguments for nested eligible expressions
            for arg in args {
                collect_candidates_inner(arg, bound_names, out);
            }
        }

        // Eligible: collection operation that references bound vars
        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            if expr_references_any_bound(receiver, bound_names)
                || args
                    .iter()
                    .any(|a| expr_references_any_bound(a, bound_names))
            {
                let covered = referenced_bound_vars(expr, bound_names);
                out.push(ScopedCandidate {
                    expr: expr.clone(),
                    covered,
                });
            }
            collect_candidates_inner(receiver, bound_names, out);
            for arg in args {
                collect_candidates_inner(arg, bound_names, out);
            }
        }

        // Eligible: indexing that references bound vars
        TrustVcExpr::Index {
            receiver, index, ..
        } => {
            if expr_references_any_bound(receiver, bound_names)
                || expr_references_any_bound(index, bound_names)
            {
                let covered = referenced_bound_vars(expr, bound_names);
                out.push(ScopedCandidate {
                    expr: expr.clone(),
                    covered,
                });
            }
            collect_candidates_inner(receiver, bound_names, out);
            collect_candidates_inner(index, bound_names, out);
        }

        // Not eligible but recurse into children
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            collect_candidates_inner(left, bound_names, out);
            collect_candidates_inner(right, bound_names, out);
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_candidates_inner(premise, bound_names, out);
            collect_candidates_inner(conclusion, bound_names, out);
        }
        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => {
            collect_candidates_inner(inner, bound_names, out);
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_candidates_inner(cond, bound_names, out);
            collect_candidates_inner(then_branch, bound_names, out);
            collect_candidates_inner(else_branch, bound_names, out);
        }
        TrustVcExpr::Cast { expr, .. } => {
            collect_candidates_inner(expr, bound_names, out);
        }
        TrustVcExpr::Let {
            name, value, body, ..
        } => {
            collect_candidates_inner(value, bound_names, out);
            // Let-bound name shadows any same-named quantifier variable
            let body_names = crate::match_pattern_scope::without_name(bound_names, name);
            collect_candidates_inner(body, body_names.as_ref().unwrap_or(bound_names), out);
        }
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_candidates_inner(scrutinee, bound_names, out);
            for arm in arms {
                let arm_scope = crate::match_pattern_scope::without_pattern_bound_names(
                    bound_names,
                    &arm.pattern,
                );
                collect_candidates_inner(&arm.body, arm_scope.as_ref().unwrap_or(bound_names), out);
            }
        }
        TrustVcExpr::Quantifier { .. } => {
            // Don't recurse into nested quantifiers — their triggers are separate
        }
        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            // Choose-bound variable shadows any same-named quantifier variable
            let inner_names = crate::match_pattern_scope::without_name(bound_names, var_name);
            collect_candidates_inner(condition, inner_names.as_ref().unwrap_or(bound_names), out);
        }
        TrustVcExpr::SpecClosure { params, body, .. } => {
            // Closure parameters shadow any same-named quantifier variables
            let param_names: Vec<&str> = params.iter().map(|(n, _)| n.as_str()).collect();
            let inner_names = crate::match_pattern_scope::without_names(bound_names, &param_names);
            collect_candidates_inner(body, inner_names.as_ref().unwrap_or(bound_names), out);
        }

        // Place expressions: recurse into index projections
        TrustVcExpr::ReadPlace { place, .. } => {
            for proj in &place.projections {
                if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                    collect_candidates_inner(index, bound_names, out);
                }
            }
        }
        TrustVcExpr::PlaceDisjoint { left, right } => {
            for place in [left, right] {
                for proj in &place.projections {
                    if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                        collect_candidates_inner(index, bound_names, out);
                    }
                }
            }
        }

        // Prophecy: ProphecyNew is a leaf; ProphecyResolve recurses into value.
        // Neither is trigger-eligible (prophecy is not an SMT pattern).
        TrustVcExpr::ProphecyNew { .. } => {}
        TrustVcExpr::ProphecyResolve { value, .. } => {
            collect_candidates_inner(value, bound_names, out);
        }

        // Leaves — nothing to collect
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => {}
    }
}
