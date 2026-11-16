// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A resolved branch/iteration cannot release a later live instance of a loan.
use super::*;

fn source(read_storage: bool, later_write: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let mut body = choose(flag, 2);
    body.extend(initial(value, loan));
    let then_block = Block::new(vec![
        write(loan, 1),
        assertion(resolved(loan), 0),
        again(0, 14),
    ]);
    let mut alternative = vec![assertion(
        if read_storage {
            eq(read(value, scalar()), integer(0))
        } else {
            resolved(loan)
        },
        1,
    )];
    if later_write {
        alternative.push(write(loan, 2));
    }
    alternative.push(again(0, 15));
    body.push(stmt(StmtKind::If {
        cond: read(flag, Ty::Bool),
        then_block,
        else_block: Block::new(alternative),
    }));
    // There is no exit; each continue drops this iteration's x and r, and
    // the same source borrow site creates a new carrier next iteration.
    f.body = Body::Stmts(Block::new(vec![isolated(0, body, vec![]), ret(None)]));
    with_choice(f)
}

#[test]
fn each_loop_borrow_branch_has_its_own_resolution_state() {
    require(
        source(false, true),
        &[(0, true, loop_group(0)), (1, false, loop_group(0))],
        0,
    );
}

#[test]
fn resolving_another_iteration_or_branch_does_not_release_borrowed_storage() {
    require_refusal(source(true, true), "mut-ref-borrowed");
}

#[test]
fn storage_is_available_when_its_current_loop_borrow_can_actually_resolve() {
    require(
        source(true, false),
        &[(0, true, loop_group(0)), (1, true, loop_group(0))],
        0,
    );
}
