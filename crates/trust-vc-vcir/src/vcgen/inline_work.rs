//! Admission before deep copies introduced by explicit body substitution.

use super::expr::R;
use super::term::Term;
use super::val::{refusal, Val};
use crate::SpanId;
use std::cell::Cell;

fn debit(work: &Cell<usize>, cost: usize, span: SpanId) -> R<()> {
    let remaining = work.get().checked_sub(cost).ok_or_else(|| {
        refusal(
            "inline-size",
            "checked inline substitution work exhausted",
            span,
        )
    })?;
    work.set(remaining);
    Ok(())
}

pub(super) fn items(work: &Cell<usize>, count: usize, span: SpanId) -> R<()> {
    debit(work, count, span)
}

pub(super) fn leaves(work: &Cell<usize>, value: &Val, span: SpanId) -> R<usize> {
    fn count(work: &Cell<usize>, value: &Val, span: SpanId, depth: usize) -> R<usize> {
        debit(work, 1, span)?;
        if depth >= 256 {
            return Err(refusal(
                "inline-size",
                "inline layout depth exhausted",
                span,
            ));
        }
        match value {
            Val::Leaf(_) => Ok(1),
            Val::Node(children) => {
                let mut total = 0usize;
                for child in children {
                    total = total
                        .checked_add(count(work, child, span, depth + 1)?)
                        .ok_or_else(|| {
                            refusal("inline-size", "inline layout leaf count overflow", span)
                        })?;
                }
                Ok(total)
            }
        }
    }
    count(work, value, span, 0)
}

/// Admission for source-key construction before the choice registry copies
/// its structural shape. This walk borrows source; it never builds a key.
pub(super) fn expression(work: &Cell<usize>, expression: &crate::Expr, span: SpanId) -> R<()> {
    fn visit(work: &Cell<usize>, expression: &crate::Expr, span: SpanId, depth: usize) -> R<()> {
        debit(work, 1, span)?;
        if depth >= 256 {
            return Err(refusal(
                "inline-size",
                "inline source depth exhausted",
                span,
            ));
        }
        fn ty(work: &Cell<usize>, value: &crate::Ty, span: SpanId, depth: usize) -> R<()> {
            debit(work, 1, span)?;
            if depth >= 64 {
                return Err(refusal("inline-size", "inline type depth exhausted", span));
            }
            match value {
                crate::Ty::Tuple(children) | crate::Ty::Adt(_, children) => {
                    for child in children {
                        ty(work, child, span, depth + 1)?;
                    }
                }
                crate::Ty::Ref { inner, .. } => ty(work, inner, span, depth + 1)?,
                _ => {}
            }
            Ok(())
        }
        ty(work, &expression.ty, span, 0)?;
        match &expression.kind {
            crate::ExprKind::Call { type_args, .. } => {
                for value in type_args {
                    ty(work, value, span, 0)?;
                }
            }
            crate::ExprKind::Read(place) | crate::ExprKind::Old(place) => {
                debit(work, place.projections.len(), span)?
            }
            crate::ExprKind::Quant { vars, .. }
            | crate::ExprKind::Choose { vars, .. }
            | crate::ExprKind::UntriggeredQuant { vars, .. }
            | crate::ExprKind::UntriggeredChoose { vars, .. } => {
                for (_, value) in vars {
                    ty(work, value, span, 0)?;
                }
            }
            // A key cannot silently omit embedded proof statements.
            crate::ExprKind::ProofInSpec(_) => {
                return Err(refusal(
                    "inline-size",
                    "a choice key with embedded proof statements",
                    span,
                ))
            }
            _ => {}
        }
        let mut result = Ok(());
        expression.for_each_child(&mut |child| {
            if result.is_ok() {
                result = visit(work, child, span, depth + 1);
            }
        });
        result
    }
    visit(work, expression, span, 0)
}

pub(super) fn value(work: &Cell<usize>, value: &Val, copies: usize, span: SpanId) -> R<()> {
    fn visit(work: &Cell<usize>, value: &Val, copies: usize, span: SpanId, depth: usize) -> R<()> {
        if depth >= 256 {
            return Err(refusal(
                "inline-size",
                "inline value copy depth exhausted",
                span,
            ));
        }
        debit(work, copies, span)?;
        match value {
            Val::Leaf(value) => term(work, value, copies, span),
            Val::Node(children) => {
                for child in children {
                    visit(work, child, copies, span, depth + 1)?;
                }
                Ok(())
            }
        }
    }
    visit(work, value, copies, span, 0)
}

pub(super) fn term(work: &Cell<usize>, value: &Term, copies: usize, span: SpanId) -> R<()> {
    fn visit(work: &Cell<usize>, value: &Term, copies: usize, span: SpanId, depth: usize) -> R<()> {
        if depth >= 256 {
            return Err(refusal(
                "inline-size",
                "inline term copy depth exhausted",
                span,
            ));
        }
        let bytes = match value {
            Term::Var { name, .. } | Term::Call { name, .. } => name.len(),
            _ => 0,
        };
        let cost = bytes
            .checked_add(1)
            .and_then(|size| size.checked_mul(copies))
            .ok_or_else(|| refusal("inline-size", "inline copy size overflow", span))?;
        debit(work, cost, span)?;
        let next = depth + 1;
        match value {
            Term::Not(inner) | Term::Neg(inner) => visit(work, inner, copies, span, next),
            Term::And(children) | Term::Or(children) | Term::Call { args: children, .. } => {
                for child in children {
                    visit(work, child, copies, span, next)?;
                }
                Ok(())
            }
            Term::Implies(left, right)
            | Term::Cmp(_, left, right)
            | Term::Arith(_, left, right) => {
                visit(work, left, copies, span, next)?;
                visit(work, right, copies, span, next)
            }
            Term::Ite(condition, yes, no, _) => {
                visit(work, condition, copies, span, next)?;
                visit(work, yes, copies, span, next)?;
                visit(work, no, copies, span, next)
            }
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => Ok(()),
        }
    }
    visit(work, value, copies, span, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vcgen::term::{ArithOp, Sort};

    #[test]
    fn repeatedly_substituting_a_scalar_argument_has_one_shared_finite_copy_grant() {
        let work = Cell::new(128);
        let mut value = Term::var("actual_argument", Sort::Int);
        let mut completed = 0;
        for _ in 0..24 {
            if term(&work, &value, 2, SpanId(0)).is_err() {
                break;
            }
            value = Term::Arith(ArithOp::Add, Box::new(value.clone()), Box::new(value));
            completed += 1;
        }
        assert!(completed > 0 && completed < 24);
        assert!(term(&work, &value, 2, SpanId(0)).is_err());
    }

    #[test]
    fn a_large_leaf_name_is_admitted_before_a_copy() {
        let value = Val::Leaf(Term::var("x".repeat(4096), Sort::Int));
        let work = Cell::new(64);
        assert!(super::value(&work, &value, 1, SpanId(0)).is_err());
    }

    #[test]
    fn deep_borrowed_input_refuses_before_recursing_or_copying_without_a_bound() {
        let mut value = Term::var("x", Sort::Int);
        for _ in 0..300 {
            value = Term::Neg(Box::new(value));
        }
        assert!(term(&Cell::new(200_000), &value, 1, SpanId(0)).is_err());
    }
}
