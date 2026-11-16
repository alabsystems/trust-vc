// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A stable future snapshot connects fresh loop carriers to outer storage.
use super::*;

fn source(correct: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let expected = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let loan_value = || read(loan, reference(scalar()));
    let mut statements = initial(value, loan);
    statements.push(write(loan, 20));
    statements.push(stmt(StmtKind::Let {
        local: expected,
        init: Some(future(loan_value())),
    }));
    let invs = vec![
        invariant(eq(future(loan_value()), read(expected, scalar()))),
        invariant(eq(current(loan_value()), integer(20))),
    ];
    let mut body = choose(flag, 1);
    body.push(stmt(StmtKind::If {
        cond: read(flag, Ty::Bool),
        then_block: Block::new(vec![leave(0, 13)]),
        else_block: Block::default(),
    }));
    body.push(write(loan, 20));
    statements.push(isolated(0, body, invs));
    statements.push(assertion(
        eq(
            read(value, scalar()),
            integer(if correct { 20 } else { 21 }),
        ),
        0,
    ));
    statements.push(ret(None));
    f.body = Body::Stmts(Block::new(statements));
    with_choice(f)
}

#[test]
fn an_explicit_future_invariant_preserves_scalar_writeback_after_the_loop() {
    require(source(true), &[(0, true, QueryGroup::Body)], 6);
}

#[test]
fn an_explicit_future_invariant_does_not_prove_a_false_scalar_writeback() {
    require(source(false), &[(0, false, QueryGroup::Body)], 6);
}
