//! Preserve raw inferred and explicitly marked prophecy across checked evaluation.
use super::*;

fn checked_value() -> Expr {
    Expr::checked_binary(
        BinOp::Add,
        Expr::int_lit(0, Ty::uint(8), span()),
        Expr::int_lit(1, Ty::uint(8), span()),
        Ty::uint(8),
        SiteId(1),
        span(),
    )
}

#[test]
fn a_prophetic_conditional_stays_prophetic_after_checked_binding() {
    for marker in [DeclProphecy::Default, DeclProphecy::DelayedInfer] {
        let mut f = function(1400, Mode::Exec, Ty::uint(8));
        f.locals[f.ret.index()].mode = Mode::Spec;
        let value = add(&mut f, Ty::uint(8), Mode::Spec, LocalKind::Let, marker);
        let init = Expr::new(
            Ty::uint(8),
            span(),
            ExprKind::If {
                cond: Box::new(call(1, Ty::Bool, vec![])),
                then_expr: Box::new(checked_value()),
                else_expr: Box::new(Expr::int_lit(2, Ty::uint(8), span())),
            },
        );
        f.body = Body::Stmts(Block::new(vec![
            stmt(StmtKind::LetChecked { local: value, init }),
            stmt(StmtKind::Return {
                value: Some(read(value, Ty::uint(8))),
                site: SiteId(2),
            }),
        ]));
        rejected(
            &source(vec![f]),
            1400,
            "prophetic value not allowed for return value",
        );
    }
}

#[test]
fn an_explicit_source_marker_is_not_cleared_by_checked_evaluation() {
    let mut f = function(1401, Mode::Exec, Ty::uint(8));
    f.locals[f.ret.index()].mode = Mode::Spec;
    let value = add(
        &mut f,
        Ty::uint(8),
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Prophetic,
    );
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::LetChecked {
            local: value,
            init: checked_value(),
        }),
        stmt(StmtKind::Return {
            value: Some(read(value, Ty::uint(8))),
            site: SiteId(2),
        }),
    ]));
    rejected(
        &source(vec![f]),
        1401,
        "prophetic value not allowed for return value",
    );
}
