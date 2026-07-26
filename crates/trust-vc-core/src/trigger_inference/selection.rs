// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use crate::ir_expr::TrustVcExpr;

use super::candidate::ScopedCandidate;

/// Check if a group of scoped candidates covers all bound variables using
/// their pre-computed coverage (which accounts for variable shadowing).
fn scoped_covers_all(group: &[&ScopedCandidate<'_>], bound_names: &HashSet<&str>) -> bool {
    let mut covered: HashSet<&str> = HashSet::new();
    for c in group {
        covered.extend(&c.covered);
    }
    covered.len() == bound_names.len()
}

/// Score a trigger candidate (lower is better).
///
/// Prefers: function calls > collection ops > indexing.
/// Smaller expressions are preferred (fewer AST nodes).
fn score_trigger(expr: &TrustVcExpr) -> u32 {
    let kind_bonus = match expr {
        TrustVcExpr::FnCall { .. } => 0,
        TrustVcExpr::CollectionOp { .. } => 10,
        TrustVcExpr::Index { .. } => 20,
        _ => 100,
    };
    kind_bonus + ast_node_count(expr)
}

fn ast_node_count(expr: &TrustVcExpr) -> u32 {
    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => 1,
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            1 + ast_node_count(left) + ast_node_count(right)
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => 1 + ast_node_count(premise) + ast_node_count(conclusion),
        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => 1 + ast_node_count(inner),
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => 1 + ast_node_count(cond) + ast_node_count(then_branch) + ast_node_count(else_branch),
        TrustVcExpr::Cast { expr, .. } => 1 + ast_node_count(expr),
        TrustVcExpr::FnCall { args, .. } => 1 + args.iter().map(ast_node_count).sum::<u32>(),
        TrustVcExpr::Let { value, body, .. } => 1 + ast_node_count(value) + ast_node_count(body),
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            1 + ast_node_count(scrutinee)
                + arms.iter().map(|a| ast_node_count(&a.body)).sum::<u32>()
        }
        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            1 + ast_node_count(receiver) + args.iter().map(ast_node_count).sum::<u32>()
        }
        TrustVcExpr::Index {
            receiver, index, ..
        } => 1 + ast_node_count(receiver) + ast_node_count(index),
        TrustVcExpr::Quantifier { body, .. } => 1 + ast_node_count(body),
        TrustVcExpr::Choose { condition, .. } => 1 + ast_node_count(condition),
        TrustVcExpr::SpecClosure { body, .. } => 1 + ast_node_count(body),
        TrustVcExpr::ReadPlace { place, .. } => {
            1 + place
                .projections
                .iter()
                .map(|p| match p {
                    crate::ir_place::PlaceProjection::Index { index, .. } => {
                        1 + ast_node_count(index)
                    }
                    crate::ir_place::PlaceProjection::Field { .. } => 1,
                })
                .sum::<u32>()
        }
        TrustVcExpr::PlaceDisjoint { left, right } => {
            1 + [left, right]
                .iter()
                .map(|place| {
                    place
                        .projections
                        .iter()
                        .map(|p| match p {
                            crate::ir_place::PlaceProjection::Index { index, .. } => {
                                1 + ast_node_count(index)
                            }
                            crate::ir_place::PlaceProjection::Field { .. } => 1,
                        })
                        .sum::<u32>()
                })
                .sum::<u32>()
        }
        TrustVcExpr::ProphecyNew { .. } => 1,
        TrustVcExpr::ProphecyResolve { value, .. } => 1 + ast_node_count(value),
    }
}

/// Conservative selection: best single trigger group, or minimal pair fallback.
pub(super) fn select_conservative(
    candidates: &[ScopedCandidate<'_>],
    bound_names: &HashSet<&str>,
) -> Vec<Vec<TrustVcExpr>> {
    // Phase 1: Try single triggers that cover all bound vars
    let mut singles: Vec<&ScopedCandidate<'_>> = candidates
        .iter()
        .filter(|c| scoped_covers_all(&[c], bound_names))
        .collect();

    if !singles.is_empty() {
        singles.sort_by_key(|c| score_trigger(&c.expr));
        if let Some(single) = singles.first() {
            return vec![vec![single.expr.clone()]];
        }
    }

    // Phase 2: Search for minimal pairs
    find_minimal_pairs(candidates, bound_names)
}

/// Aggressive selection: all valid single triggers, plus pairs as fallback.
pub(super) fn select_aggressive(
    candidates: &[ScopedCandidate<'_>],
    bound_names: &HashSet<&str>,
) -> Vec<Vec<TrustVcExpr>> {
    let mut singles: Vec<&ScopedCandidate<'_>> = candidates
        .iter()
        .filter(|c| scoped_covers_all(&[c], bound_names))
        .collect();

    if !singles.is_empty() {
        singles.sort_by_key(|c| score_trigger(&c.expr));
        return singles.iter().map(|c| vec![c.expr.clone()]).collect();
    }

    find_minimal_pairs(candidates, bound_names)
}

/// Find minimal pairs of candidates whose union covers all bound vars.
/// Cap at 3 groups to avoid combinatorial explosion.
fn find_minimal_pairs(
    candidates: &[ScopedCandidate<'_>],
    bound_names: &HashSet<&str>,
) -> Vec<Vec<TrustVcExpr>> {
    let mut groups = Vec::new();
    for (i, a) in candidates.iter().enumerate() {
        for b in candidates.iter().skip(i + 1) {
            if scoped_covers_all(&[a, b], bound_names) {
                groups.push(vec![a.expr.clone(), b.expr.clone()]);
                if groups.len() >= 3 {
                    return groups;
                }
            }
        }
    }
    groups
}
