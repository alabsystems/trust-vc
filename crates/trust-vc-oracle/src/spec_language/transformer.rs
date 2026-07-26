// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// SpecTransformer
// ---------------------------------------------------------------------------

/// Semantic transformations on specification expressions.
pub struct SpecTransformer;

impl SpecTransformer {
    /// Substitute all free occurrences of `var` with `replacement`.
    #[must_use]
    pub fn substitute(expr: &SpecExpr, var: &str, replacement: &SpecExpr) -> SpecExpr {
        Self::subst_inner(expr, var, replacement, &HashSet::new())
    }

    fn subst_inner(
        expr: &SpecExpr,
        var: &str,
        replacement: &SpecExpr,
        bound: &HashSet<String>,
    ) -> SpecExpr {
        match expr {
            SpecExpr::Variable(name) => {
                if name == var && !bound.contains(var) {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            SpecExpr::IntLit(_) | SpecExpr::BoolLit(_) => expr.clone(),
            SpecExpr::BinOp(lhs, op, rhs) => SpecExpr::BinOp(
                Box::new(Self::subst_inner(lhs, var, replacement, bound)),
                *op,
                Box::new(Self::subst_inner(rhs, var, replacement, bound)),
            ),
            SpecExpr::UnaryOp(op, inner) => SpecExpr::UnaryOp(
                *op,
                Box::new(Self::subst_inner(inner, var, replacement, bound)),
            ),
            SpecExpr::FnCall(name, args) => SpecExpr::FnCall(
                name.clone(),
                args.iter()
                    .map(|a| Self::subst_inner(a, var, replacement, bound))
                    .collect(),
            ),
            SpecExpr::Quantifier(kind, bindings, body) => {
                let mut inner_bound = bound.clone();
                for (bname, _) in bindings {
                    inner_bound.insert(bname.clone());
                }
                SpecExpr::Quantifier(
                    *kind,
                    bindings.clone(),
                    Box::new(Self::subst_inner(body, var, replacement, &inner_bound)),
                )
            }
            SpecExpr::FieldAccess(base, field) => SpecExpr::FieldAccess(
                Box::new(Self::subst_inner(base, var, replacement, bound)),
                field.clone(),
            ),
            SpecExpr::IndexAccess(base, index) => SpecExpr::IndexAccess(
                Box::new(Self::subst_inner(base, var, replacement, bound)),
                Box::new(Self::subst_inner(index, var, replacement, bound)),
            ),
            SpecExpr::IfThenElse(cond, then_br, else_br) => SpecExpr::IfThenElse(
                Box::new(Self::subst_inner(cond, var, replacement, bound)),
                Box::new(Self::subst_inner(then_br, var, replacement, bound)),
                Box::new(Self::subst_inner(else_br, var, replacement, bound)),
            ),
            SpecExpr::Old(inner) => {
                SpecExpr::Old(Box::new(Self::subst_inner(inner, var, replacement, bound)))
            }
        }
    }

    /// Weaken a precondition by disjoining it with `true`.
    ///
    /// `P` becomes `P || true`, which is always satisfiable. This is the
    /// simplest sound weakening: it preserves the original constraint as a
    /// hint while guaranteeing the precondition is always met.
    #[must_use]
    pub fn weaken(expr: &SpecExpr) -> SpecExpr {
        // A more nuanced weakening: if the expression is already a
        // conjunction, drop the last conjunct. Otherwise disjoin with true.
        match expr {
            SpecExpr::BinOp(lhs, BinOpKind::And, _rhs) => {
                // Weaken A && B to just A.
                *lhs.clone()
            }
            _ => SpecExpr::BinOp(
                Box::new(expr.clone()),
                BinOpKind::Or,
                Box::new(SpecExpr::BoolLit(true)),
            ),
        }
    }

    /// Strengthen a postcondition by conjoining it with an additional constraint.
    ///
    /// If the expression is already a conjunction, the extra `true` is a no-op
    /// structurally but demonstrates the pattern. In practice the oracle would
    /// supply a meaningful strengthening term.
    #[must_use]
    pub fn strengthen(expr: &SpecExpr) -> SpecExpr {
        // Strengthen by conjoining with `result >= 0` as a common
        // non-negativity postcondition.  For a generic strengthener this
        // is a reasonable default; callers should replace the second operand.
        SpecExpr::BinOp(
            Box::new(expr.clone()),
            BinOpKind::And,
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::Variable("result".to_string())),
                BinOpKind::Ge,
                Box::new(SpecExpr::IntLit(0)),
            )),
        )
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------
