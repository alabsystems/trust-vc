//! Borrowed resource pricing, without expression/statement eligibility grants.
//!
//! Auxiliary pure-skip still uses the caller's retained inline work cell.
//! Unlike checked-inline substitution, proof payloads are priced here rather
//! than rejected. This walk emits no term, key, proof event or assumption.

use super::{expr::R, inline_work::items, val::refusal};
use crate::{Block, ClauseAttrs, Expr, ExprKind, Place, SpanId, Stmt, StmtKind, Ty};
use std::cell::Cell;

pub(super) fn expression(work: &Cell<usize>, source: &Expr, span: SpanId) -> R<()> {
    expression_at(work, source, span, 0)
}

fn node(work: &Cell<usize>, span: SpanId, depth: usize) -> R<()> {
    items(work, 1, span)?;
    if depth >= 256 {
        return Err(refusal(
            "inline-size",
            "auxiliary source depth exhausted",
            span,
        ));
    }
    Ok(())
}

fn ty(work: &Cell<usize>, source: &Ty, span: SpanId, depth: usize) -> R<()> {
    items(work, 1, span)?;
    if depth >= 64 {
        return Err(refusal(
            "inline-size",
            "auxiliary type depth exhausted",
            span,
        ));
    }
    match source {
        Ty::Tuple(children) | Ty::Adt(_, children) => {
            for child in children {
                ty(work, child, span, depth + 1)?;
            }
        }
        Ty::Ref { inner, .. } => ty(work, inner, span, depth + 1)?,
        Ty::Bool | Ty::Int(_) | Ty::Unit | Ty::Param(_) => {}
    }
    Ok(())
}

fn place(work: &Cell<usize>, source: &Place, span: SpanId) -> R<()> {
    items(work, 1, span)?;
    items(work, source.projections.len(), span)
}

fn attributes(work: &Cell<usize>, source: &ClauseAttrs, span: SpanId) -> R<()> {
    for text in source.proof_notes.iter().chain(&source.custom_errs) {
        items(work, 1, span)?;
        items(work, text.len(), span)?;
    }
    Ok(())
}

fn expression_at(work: &Cell<usize>, source: &Expr, span: SpanId, depth: usize) -> R<()> {
    node(work, span, depth)?;
    ty(work, &source.ty, span, 0)?;
    match &source.kind {
        ExprKind::Lit(_) | ExprKind::IntegerConstant(_) => {}
        ExprKind::Read(value) | ExprKind::Old(value) => place(work, value, span)?,
        ExprKind::Unary { arg, .. } | ExprKind::Cast { arg, .. } | ExprKind::Borrow(arg) => {
            expression_at(work, arg, span, depth + 1)?
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            expression_at(work, lhs, span, depth + 1)?;
            expression_at(work, rhs, span, depth + 1)?;
        }
        ExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            expression_at(work, cond, span, depth + 1)?;
            expression_at(work, then_expr, span, depth + 1)?;
            expression_at(work, else_expr, span, depth + 1)?;
        }
        ExprKind::Let { value, body, .. } => {
            expression_at(work, value, span, depth + 1)?;
            expression_at(work, body, span, depth + 1)?;
        }
        ExprKind::Call {
            type_args, args, ..
        } => {
            for argument in type_args {
                ty(work, argument, span, 0)?;
            }
            for argument in args {
                expression_at(work, argument, span, depth + 1)?;
            }
        }
        ExprKind::Ctor { fields, .. } | ExprKind::Tuple(fields) => {
            for field in fields {
                expression_at(work, field, span, depth + 1)?;
            }
        }
        ExprKind::IsVariant { base, .. }
        | ExprKind::Field { base, .. }
        | ExprKind::TupleField { base, .. } => expression_at(work, base, span, depth + 1)?,
        ExprKind::ProofInSpec(value) => block(work, value, span, depth + 1)?,
        ExprKind::Quant {
            vars,
            triggers,
            body,
            ..
        } => {
            binders(work, vars, span)?;
            hints(work, triggers, span, depth + 1)?;
            expression_at(work, body, span, depth + 1)?;
        }
        ExprKind::Choose {
            vars,
            triggers,
            cond,
            result,
        } => {
            binders(work, vars, span)?;
            hints(work, triggers, span, depth + 1)?;
            expression_at(work, cond, span, depth + 1)?;
            expression_at(work, result, span, depth + 1)?;
        }
        ExprKind::UntriggeredQuant {
            vars,
            trigger_candidates,
            body,
            ..
        } => {
            binders(work, vars, span)?;
            for hint in trigger_candidates {
                expression_at(work, hint, span, depth + 1)?;
            }
            expression_at(work, body, span, depth + 1)?;
        }
        ExprKind::UntriggeredChoose {
            vars,
            trigger_candidates,
            cond,
            result,
        } => {
            binders(work, vars, span)?;
            for hint in trigger_candidates {
                expression_at(work, hint, span, depth + 1)?;
            }
            expression_at(work, cond, span, depth + 1)?;
            expression_at(work, result, span, depth + 1)?;
        }
    }
    Ok(())
}

fn binders(work: &Cell<usize>, source: &[(crate::LocalId, Ty)], span: SpanId) -> R<()> {
    for (_, value) in source {
        items(work, 1, span)?;
        ty(work, value, span, 0)?;
    }
    Ok(())
}

fn hints(work: &Cell<usize>, source: &[Vec<Expr>], span: SpanId, depth: usize) -> R<()> {
    for group in source {
        items(work, 1, span)?;
        for value in group {
            expression_at(work, value, span, depth)?;
        }
    }
    Ok(())
}

fn block(work: &Cell<usize>, source: &Block, span: SpanId, depth: usize) -> R<()> {
    node(work, span, depth)?;
    for statement in &source.stmts {
        stmt(work, statement, span, depth + 1)?;
    }
    Ok(())
}

fn stmt(work: &Cell<usize>, source: &Stmt, span: SpanId, depth: usize) -> R<()> {
    node(work, span, depth)?;
    match &source.kind {
        StmtKind::Let { init, .. } | StmtKind::Return { value: init, .. } => {
            if let Some(value) = init {
                expression_at(work, value, span, depth + 1)?;
            }
        }
        StmtKind::Assign {
            place: target,
            value,
        } => {
            place(work, target, span)?;
            expression_at(work, value, span, depth + 1)?;
        }
        StmtKind::Call {
            type_args,
            args,
            dest,
            ..
        } => {
            for argument in type_args {
                ty(work, argument, span, 0)?;
            }
            for argument in args {
                expression_at(work, argument, span, depth + 1)?;
            }
            if let Some(target) = dest {
                place(work, target, span)?;
            }
        }
        StmtKind::Assert { expr, attrs, .. } | StmtKind::Assume { expr, attrs } => {
            attributes(work, attrs, span)?;
            expression_at(work, expr, span, depth + 1)?;
        }
        StmtKind::AssertBitVector {
            requires, ensures, ..
        } => {
            for clause in requires.iter().chain(ensures) {
                items(work, 1, span)?;
                attributes(work, &clause.attrs, span)?;
                expression_at(work, &clause.expr, span, depth + 1)?;
            }
        }
        StmtKind::If {
            cond,
            then_block,
            else_block,
        } => {
            expression_at(work, cond, span, depth + 1)?;
            block(work, then_block, span, depth + 1)?;
            block(work, else_block, span, depth + 1)?;
        }
        StmtKind::Ghost(value) | StmtKind::Block(value) => block(work, value, span, depth + 1)?,
        StmtKind::Loop(value) => {
            node(work, span, depth + 1)?;
            if let Some(condition) = &value.cond {
                block(work, &condition.block, span, depth + 2)?;
                expression_at(work, &condition.expr, span, depth + 2)?;
            }
            for invariant in &value.invariants {
                items(work, 1, span)?;
                expression_at(work, &invariant.expr, span, depth + 2)?;
            }
            for measure in &value.decreases {
                expression_at(work, measure, span, depth + 2)?;
            }
            block(work, &value.body, span, depth + 2)?;
        }
        StmtKind::Reveal { .. }
        | StmtKind::Hide { .. }
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Unreachable => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_payloads_are_priced_with_exact_and_one_short_shared_remainders() {
        let source = Expr::new(
            Ty::Unit,
            SpanId(0),
            ExprKind::ProofInSpec(Block::new(vec![Stmt::new(
                SpanId(0),
                StmtKind::Assume {
                    expr: Expr::bool_lit(true, SpanId(0)),
                    attrs: ClauseAttrs {
                        proof_notes: vec!["note".repeat(1024)],
                        custom_errs: vec![],
                    },
                },
            )])),
        );
        let measured = Cell::new(200_000);
        expression(&measured, &source, SpanId(0)).unwrap();
        let used = 200_000 - measured.get();
        assert!(used > 4096);
        let exact = Cell::new(used);
        expression(&exact, &source, SpanId(0)).unwrap();
        assert_eq!(exact.get(), 0);
        let short = Cell::new(used - 1);
        assert!(expression(&short, &source, SpanId(0)).is_err());
        assert!(
            super::super::inline_work::expression(&Cell::new(200_000), &source, SpanId(0)).is_err(),
            "resource admission does not change checked-inline eligibility"
        );
    }
}
