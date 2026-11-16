// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Moving out and reinitializing preserves the carrier without resolving it.
use super::*;

fn source(reinitialize: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Param);
    f.locals[loan.0 as usize].mutable = true;
    let expected = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let moved = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let loan_value = || read(loan, reference(scalar()));
    let preservation = || eq(future(loan_value()), read(expected, scalar()));
    let mut body = vec![stmt(StmtKind::Let {
        local: moved,
        init: Some(loan_value()),
    })];
    if reinitialize {
        body.push(stmt(StmtKind::Assign {
            place: Place::local(loan),
            value: read(moved, reference(scalar())),
        }));
    }
    body.push(assertion(preservation(), 0));
    body.push(assertion(resolved(loan), 1));
    body.extend(choose(flag, 2));
    body.push(stmt(StmtKind::If {
        cond: read(flag, Ty::Bool),
        then_block: Block::new(vec![leave(0, 13)]),
        else_block: Block::default(),
    }));
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: expected,
            init: Some(future(loan_value())),
        }),
        isolated(0, body, vec![invariant(preservation())]),
        ret(None),
    ]));
    with_choice(f)
}

#[test]
fn a_reinitialized_loop_owner_preserves_future_without_premature_resolution() {
    require(
        source(true),
        &[(0, true, loop_group(0)), (1, false, loop_group(0))],
        3,
    );
}

#[test]
fn an_owner_moved_in_the_loop_is_unavailable_until_reinitialized() {
    require_refusal(source(false), "mut-ref-moved");
}
