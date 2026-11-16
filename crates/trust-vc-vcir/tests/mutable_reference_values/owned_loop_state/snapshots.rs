// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A Spec carrier snapshot never consumes its executable owner at a loop cut.
use super::*;

#[test]
fn a_spec_reference_snapshot_preserves_the_exec_owner_across_loop_cuts() {
    let mut f = function(Ty::Unit);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Param);
    let snapshot = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Let);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let mut body = vec![stmt(StmtKind::Block(Block::new(vec![stmt(
        StmtKind::Let {
            local: snapshot,
            init: Some(read(loan, reference(scalar()))),
        },
    )])))];
    body.push(write(loan, 7));
    body.push(assertion(
        eq(current(read(loan, reference(scalar()))), integer(7)),
        0,
    ));
    body.extend(choose(flag, 2));
    body.push(stmt(StmtKind::If {
        cond: read(flag, Ty::Bool),
        then_block: Block::new(vec![leave(0, 13)]),
        else_block: Block::default(),
    }));
    f.body = Body::Stmts(Block::new(vec![
        isolated(0, body, vec![]),
        write(loan, 8),
        assertion(eq(current(read(loan, reference(scalar()))), integer(8)), 1),
        ret(None),
    ]));
    require(
        with_choice(f),
        &[(0, true, loop_group(0)), (1, true, QueryGroup::Body)],
        0,
    );
}

#[test]
fn a_ghost_tail_spec_reference_let_does_not_move_or_return_the_exec_owner() {
    let mut f = function(Ty::Unit);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Param);
    let snapshot = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Bound);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let tail = Expr::new(
        Ty::Unit,
        span(),
        ExprKind::Let {
            local: snapshot,
            value: Box::new(read(loan, reference(scalar()))),
            body: Box::new(Expr::new(Ty::Unit, span(), ExprKind::Lit(Lit::Unit))),
        },
    );
    let mut body = vec![stmt(StmtKind::GhostTail {
        block: Block::default(),
        tail,
    })];
    body.push(write(loan, 7));
    body.push(assertion(
        eq(current(read(loan, reference(scalar()))), integer(7)),
        0,
    ));
    body.extend(choose(flag, 2));
    body.push(stmt(StmtKind::If {
        cond: read(flag, Ty::Bool),
        then_block: Block::new(vec![leave(0, 13)]),
        else_block: Block::default(),
    }));
    f.body = Body::Stmts(Block::new(vec![
        isolated(0, body, vec![]),
        write(loan, 8),
        assertion(eq(current(read(loan, reference(scalar()))), integer(8)), 1),
        ret(None),
    ]));
    require(
        with_choice(f),
        &[(0, true, loop_group(0)), (1, true, QueryGroup::Body)],
        0,
    );
}
