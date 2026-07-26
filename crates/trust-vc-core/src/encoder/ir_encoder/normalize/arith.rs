// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Arithmetic normalization: flatten, sort, rebuild, distribute, cancel.
//! Extracted from monolithic normalize.rs as part of #2476.

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, TrustVcExpr};
use crate::ir_expr_traversal::{fold_expr_children, TrustVcExprFolder};

/// Returns true for exact arithmetic carriers where addition and
/// multiplication form commutative semirings. This includes Int-mode types and
/// mathematical reals, but deliberately excludes IEEE floats (NaN and signed
/// zero make their algebraic identities non-structural).
fn is_exact_arithmetic_type(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real
    ) || ty.is_integer()
}

/// Folder that normalizes only the expression forms that currently recurse.
struct IntNormalizer;

impl TrustVcExprFolder for IntNormalizer {
    fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
        match expr {
            TrustVcExpr::Arith {
                op,
                left,
                right,
                ty,
            } if is_exact_arithmetic_type(&ty) => {
                let left_n = self.fold_expr(*left);
                let right_n = self.fold_expr(*right);

                if matches!(op, ArithOp::Add | ArithOp::Mul) {
                    let mut operands = Vec::new();
                    flatten_assoc(op, &left_n, &mut operands);
                    flatten_assoc(op, &right_n, &mut operands);

                    // Distribution: for Mul, if exactly one operand is a sum
                    // or difference, distribute the product over its terms.
                    // This converts d * (a + b) → d*a + d*b and
                    // d * (a - b) → d*a - d*b for polynomial normalization.
                    // Gated to exactly one Add/Sub to avoid exponential blowup
                    // from products such as (a+b)*(c+d). Part of #2400.
                    if op == ArithOp::Mul {
                        let distributive_count = operands
                            .iter()
                            .filter(|o| {
                                matches!(
                                    o,
                                    TrustVcExpr::Arith {
                                        op: ArithOp::Add | ArithOp::Sub,
                                        ty: t,
                                        ..
                                    } if is_exact_arithmetic_type(t)
                                )
                            })
                            .count();

                        if distributive_count == 1 {
                            let Some(distributive_idx) = operands.iter().position(|o| {
                                matches!(
                                    o,
                                    TrustVcExpr::Arith {
                                        op: ArithOp::Add | ArithOp::Sub,
                                        ty: t,
                                        ..
                                    } if is_exact_arithmetic_type(t)
                                )
                            }) else {
                                operands.sort_by_key(expr_sort_key);
                                return rebuild_left_assoc(op, ty.clone(), operands);
                            };

                            if !operands.is_empty() {
                                let distributive_expr = operands.remove(distributive_idx);
                                // Build the normalized product of remaining factors.
                                operands.sort_by_key(expr_sort_key);
                                let factor =
                                    rebuild_left_assoc(ArithOp::Mul, ty.clone(), operands.clone());

                                match distributive_expr {
                                    TrustVcExpr::Arith {
                                        op: ArithOp::Add, ..
                                    } => {
                                        let mut sum_terms = Vec::new();
                                        flatten_assoc(
                                            ArithOp::Add,
                                            &distributive_expr,
                                            &mut sum_terms,
                                        );

                                        // Distribute: factor * (t1 + t2 + ...) → factor*t1 + factor*t2 + ...
                                        // Each distributed product is re-normalized (flatten+sort).
                                        let distributed: Vec<TrustVcExpr> = sum_terms
                                            .into_iter()
                                            .map(|term| {
                                                self.fold_expr(TrustVcExpr::Arith {
                                                    op: ArithOp::Mul,
                                                    left: Box::new(factor.clone()),
                                                    right: Box::new(term),
                                                    ty: ty.clone(),
                                                })
                                            })
                                            .collect();

                                        let mut sorted = distributed;
                                        sorted.sort_by_key(expr_sort_key);
                                        return rebuild_left_assoc(
                                            ArithOp::Add,
                                            ty.clone(),
                                            sorted,
                                        );
                                    }
                                    TrustVcExpr::Arith {
                                        op: ArithOp::Sub,
                                        left,
                                        right,
                                        ..
                                    } => {
                                        let distributed_left = self.fold_expr(TrustVcExpr::Arith {
                                            op: ArithOp::Mul,
                                            left: Box::new(factor.clone()),
                                            right: left,
                                            ty: ty.clone(),
                                        });
                                        let distributed_right =
                                            self.fold_expr(TrustVcExpr::Arith {
                                                op: ArithOp::Mul,
                                                left: Box::new(factor),
                                                right,
                                                ty: ty.clone(),
                                            });

                                        return TrustVcExpr::Arith {
                                            op: ArithOp::Sub,
                                            left: Box::new(distributed_left),
                                            right: Box::new(distributed_right),
                                            ty,
                                        };
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }

                    operands.sort_by_key(expr_sort_key);
                    rebuild_left_assoc(op, ty, operands)
                } else {
                    TrustVcExpr::Arith {
                        op,
                        left: Box::new(left_n),
                        right: Box::new(right_n),
                        ty,
                    }
                }
            }

            compare @ TrustVcExpr::Compare { .. } => {
                let TrustVcExpr::Compare { op, left, right } = fold_expr_children(self, compare)
                else {
                    unreachable!("compare match arm must rebuild to Compare")
                };

                // For equalities between exact-arithmetic sums, cancel common addends.
                // This turns `(d*q)*q2 + r == (d*q)*q2 + d*q3` into `r == d*q3`,
                // closing the GCD chain where ay-dpll lacks Int cancellation. #2400.
                if matches!(op, CompareOp::Eq) {
                    let ty = match (&*left, &*right) {
                        (TrustVcExpr::Arith { ty, .. }, _) | (_, TrustVcExpr::Arith { ty, .. })
                            if is_exact_arithmetic_type(ty) =>
                        {
                            Some(ty.clone())
                        }
                        _ => None,
                    };
                    if let Some(ty) = ty {
                        if let Some(simplified) = try_cancel_common_addends(&left, &right, &ty) {
                            return simplified;
                        }
                    }
                }

                TrustVcExpr::Compare { op, left, right }
            }

            expr @ (TrustVcExpr::Logic { .. }
            | TrustVcExpr::Not(_)
            | TrustVcExpr::Implies { .. }
            | TrustVcExpr::Neg(_)
            | TrustVcExpr::Ite { .. }) => fold_expr_children(self, expr),

            other => other,
        }
    }
}

/// Normalize a TrustVcExpr for exact arithmetic canonicalization.
///
/// Recursively normalizes all sub-expressions. For `Arith` nodes with
/// commutative+associative ops (Add, Mul) over integer, Nat, MathInt, or Real:
/// flattens nested same-op trees, sorts operands, rebuilds left-associative.
/// IEEE floating-point expressions are left in source order.
pub(crate) fn normalize_int_expr(expr: &TrustVcExpr) -> TrustVcExpr {
    IntNormalizer.fold_expr(expr.clone())
}

/// Flatten a nested tree of the same associative operator into a flat list.
///
/// For `Add`: `(a + b) + c` → `[a, b, c]`
/// For `Mul`: `a * (b * c)` → `[a, b, c]`
///
/// Only flattens when the nested Arith has the same op and an exact arithmetic
/// type supported by this normalizer.
fn flatten_assoc(target_op: ArithOp, expr: &TrustVcExpr, out: &mut Vec<TrustVcExpr>) {
    if let TrustVcExpr::Arith {
        op,
        left,
        right,
        ty,
    } = expr
    {
        if *op == target_op && is_exact_arithmetic_type(ty) {
            flatten_assoc(target_op, left, out);
            flatten_assoc(target_op, right, out);
            return;
        }
    }
    out.push(expr.clone());
}

/// Rebuild a flat operand list into a left-associative binary tree.
///
/// `[a, b, c]` with `Mul` → `((a * b) * c)`
fn rebuild_left_assoc(op: ArithOp, ty: TrustVcType, operands: Vec<TrustVcExpr>) -> TrustVcExpr {
    debug_assert!(!operands.is_empty(), "Cannot rebuild empty operand list");

    let mut iter = operands.into_iter();
    let mut acc = iter.next().unwrap_or_else(|| TrustVcExpr::IntLit {
        value: if op == ArithOp::Mul { 1 } else { 0 },
        ty: ty.clone(),
    });
    for operand in iter {
        acc = TrustVcExpr::Arith {
            op,
            left: Box::new(acc),
            right: Box::new(operand),
            ty: ty.clone(),
        };
    }
    acc
}

// =================================================================
// Additive cancellation
// =================================================================

/// Cancel common addends in an equality between exact-arithmetic sums.
///
/// Given `A + r == A + B` (where A appears on both sides), returns
/// `r == B`. Requires both sides to have remaining terms after cancellation.
/// This compensates for ay-dpll lacking Int-mode additive cancellation.
/// Part of #2400.
pub(super) fn try_cancel_common_addends(
    left: &TrustVcExpr,
    right: &TrustVcExpr,
    ty: &TrustVcType,
) -> Option<TrustVcExpr> {
    if !is_exact_arithmetic_type(ty) {
        return None;
    }

    let mut left_terms = Vec::new();
    flatten_assoc(ArithOp::Add, left, &mut left_terms);
    let mut right_terms = Vec::new();
    flatten_assoc(ArithOp::Add, right, &mut right_terms);

    // Cancel common terms (by structural equality on normalized exprs).
    let mut cancelled = false;
    let mut i = 0;
    while let Some(left_term) = left_terms.get(i).cloned() {
        if let Some(j) = right_terms.iter().position(|rt| *rt == left_term) {
            left_terms.remove(i);
            right_terms.remove(j);
            cancelled = true;
        } else {
            i += 1;
        }
    }

    if !cancelled || left_terms.is_empty() || right_terms.is_empty() {
        return None;
    }

    let new_left = rebuild_left_assoc(ArithOp::Add, ty.clone(), left_terms);
    let new_right = rebuild_left_assoc(ArithOp::Add, ty.clone(), right_terms);

    Some(TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(new_left),
        right: Box::new(new_right),
    })
}

/// Canonical sort key for TrustVcExpr operands.
///
/// Ordering: literals first (by value), then variables (by name),
/// then compound expressions (by structural representation).
fn expr_sort_key(expr: &TrustVcExpr) -> ExprSortKey {
    match expr {
        TrustVcExpr::IntLit { value, .. } => ExprSortKey::Literal(*value),
        TrustVcExpr::Var { name, .. } => ExprSortKey::Variable(name.clone()),
        _ => ExprSortKey::Compound(format!("{:?}", expr)),
    }
}

/// Sort key for canonical ordering of operands.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ExprSortKey {
    /// Literals sort first, by their numeric value.
    Literal(i128),
    /// Variables sort second, by name.
    Variable(String),
    /// Compound expressions sort last, by debug representation.
    Compound(String),
}
