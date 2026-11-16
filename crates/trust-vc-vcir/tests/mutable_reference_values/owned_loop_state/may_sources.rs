// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Possible blocking sources never become simultaneous value-write aliases.
use super::*;

fn source(both_changed: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Param);
    let x = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let y = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let parent = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let child = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let at = |place| {
        stmt(StmtKind::BorrowMut {
            dest: parent,
            place: Place::local(place),
        })
    };
    let conjunction = |a, b| Expr::binary(BinOp::And, a, b, Ty::Bool, span());
    let outcome = if both_changed {
        conjunction(
            eq(read(x, scalar()), integer(5)),
            eq(read(y, scalar()), integer(5)),
        )
    } else {
        Expr::new(
            Ty::Bool,
            span(),
            ExprKind::If {
                cond: Box::new(read(flag, Ty::Bool)),
                then_expr: Box::new(conjunction(
                    eq(read(x, scalar()), integer(5)),
                    eq(read(y, scalar()), integer(0)),
                )),
                else_expr: Box::new(conjunction(
                    eq(read(x, scalar()), integer(0)),
                    eq(read(y, scalar()), integer(5)),
                )),
            },
        )
    };
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: x,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: y,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: parent,
            init: None,
        }),
        stmt(StmtKind::If {
            cond: read(flag, Ty::Bool),
            then_block: Block::new(vec![at(x)]),
            else_block: Block::new(vec![at(y)]),
        }),
        isolated(0, vec![leave(0, 13)], vec![]),
        stmt(StmtKind::Let {
            local: child,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: child,
            place: Place::deref(parent),
        }),
        write(child, 5),
        assertion(outcome, 0),
        ret(None),
    ]));
    krate(f)
}

#[test]
fn a_postcut_reborrow_writes_only_the_selected_parent_source() {
    require(source(false), &[(0, true, QueryGroup::Body)], 0);
}

#[test]
fn possible_parent_sources_are_not_both_overwritten_by_one_reborrow() {
    require(source(true), &[(0, false, QueryGroup::Body)], 0);
}
