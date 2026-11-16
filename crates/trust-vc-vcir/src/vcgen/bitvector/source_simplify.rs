//! A bounded subset of Verus's typed syntactic equality, before BV conversion.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This compares source values, ignoring only diagnostic spans. It does not
//! identify independently lowered arbitrary zero-division results. Checked
//! operations, embedded proofs and unrepresented effects are never removed.
use super::*;

pub(super) fn comparison(lower: &mut Lower<'_, '_>, expr: &Expr, depth: usize) -> R<Option<bool>> {
    let ExprKind::Binary {
        op: BinOp::Eq | BinOp::Ne,
        lhs,
        rhs,
        check: None,
    } = &expr.kind
    else {
        return Ok(None);
    };
    if expr.ty != Ty::Bool || !same(lower, lhs, rhs, depth + 1)? {
        return Ok(None);
    }
    Ok(Some(matches!(
        expr.kind,
        ExprKind::Binary { op: BinOp::Eq, .. }
    )))
}

fn same_type(lower: &mut Lower<'_, '_>, left: &Ty, right: &Ty, at: &Expr, depth: usize) -> R<bool> {
    lower.debit(at, 4)?;
    if depth >= 64 {
        return lower.error(at, "syntactic BV type comparison depth exhausted");
    }
    Ok(match (left, right) {
        (Ty::Bool, Ty::Bool) | (Ty::Unit, Ty::Unit) => true,
        (Ty::Int(a), Ty::Int(b)) => a.is_valid() && a == b,
        (
            Ty::Ref {
                mutable: a,
                inner: x,
            },
            Ty::Ref {
                mutable: b,
                inner: y,
            },
        ) => a == b && same_type(lower, x, y, at, depth + 1)?,
        (Ty::MutRef(x), Ty::MutRef(y)) => same_type(lower, x, y, at, depth + 1)?,
        (Ty::Tuple(xs), Ty::Tuple(ys)) => same_types(lower, xs, ys, at, depth + 1)?,
        (Ty::Adt(a, xs), Ty::Adt(b, ys)) if a == b => {
            let valid = lower
                .ctx
                .adts
                .get(a)
                .is_some_and(|decl| decl.type_params.len() == xs.len());
            valid && same_types(lower, xs, ys, at, depth + 1)?
        }
        // An unclosed parameter cannot gain source interpretation by matching
        // its numeric index; live lowering still performs its usual refusal.
        _ => false,
    })
}

fn same_types(
    lower: &mut Lower<'_, '_>,
    left: &[Ty],
    right: &[Ty],
    at: &Expr,
    depth: usize,
) -> R<bool> {
    lower.debit(at, left.len().saturating_add(right.len()).saturating_add(1))?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !same_type(lower, left, right, at, depth)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_place(lower: &mut Lower<'_, '_>, left: &Place, right: &Place, at: &Expr) -> R<bool> {
    lower.debit(
        at,
        left.projections
            .len()
            .saturating_add(right.projections.len())
            .saturating_add(2),
    )?;
    Ok(left.local == right.local && left.projections == right.projections)
}

fn same(lower: &mut Lower<'_, '_>, left: &Expr, right: &Expr, depth: usize) -> R<bool> {
    lower.debit(left, 4)?;
    if depth >= 256 {
        return lower.error(left, "syntactic BV expression comparison depth exhausted");
    }
    if !same_type(lower, &left.ty, &right.ty, left, 0)? {
        return Ok(false);
    }
    let next = depth + 1;
    Ok(match (&left.kind, &right.kind) {
        (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
        (ExprKind::IntegerConstant(a), ExprKind::IntegerConstant(b)) => {
            a == b && a.value(lower.architecture).is_some()
        }
        (ExprKind::Read(a), ExprKind::Read(b)) | (ExprKind::Old(a), ExprKind::Old(b)) => {
            if !same_place(lower, a, b, left)? {
                return Ok(false);
            }
            let old = matches!(left.kind, ExprKind::Old(_));
            lower.available_place(left, a, old)?;
            lower.available_place(right, b, old)?;
            true
        }
        (
            ExprKind::Unary {
                op: a,
                arg: x,
                check: None,
            },
            ExprKind::Unary {
                op: b,
                arg: y,
                check: None,
            },
        ) => a == b && same(lower, x, y, next)?,
        (
            ExprKind::Binary {
                op: a,
                lhs: x,
                rhs: y,
                check: None,
            },
            ExprKind::Binary {
                op: b,
                lhs: z,
                rhs: w,
                check: None,
            },
        ) => a == b && same(lower, x, z, next)? && same(lower, y, w, next)?,
        (ExprKind::Cast { arg: x, kind: a }, ExprKind::Cast { arg: y, kind: b }) => {
            a == b && same(lower, x, y, next)?
        }
        (
            ExprKind::If {
                cond: a,
                then_expr: b,
                else_expr: c,
            },
            ExprKind::If {
                cond: x,
                then_expr: y,
                else_expr: z,
            },
        ) => same(lower, a, x, next)? && same(lower, b, y, next)? && same(lower, c, z, next)?,
        // Calls/proofs and reference operations can carry side conditions or
        // namespaces beyond this fragment. Preserve their original lowering.
        _ => false,
    })
}

#[cfg(test)]
mod tests;
