// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A labeled continue ends the right owned-value scope and backedge.
use super::*;

fn source(continue_outer: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let outer_flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let inner_flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Let);
    let mut outer = choose(outer_flag, 1);
    outer.push(stmt(StmtKind::If {
        cond: read(outer_flag, Ty::Bool),
        then_block: Block::new(vec![leave(0, 13)]),
        else_block: Block::default(),
    }));
    outer.extend(initial(value, loan));
    let mut inner = choose(inner_flag, 2);
    inner.push(stmt(StmtKind::If {
        cond: read(inner_flag, Ty::Bool),
        then_block: Block::new(vec![
            assertion(resolved(loan), 0),
            again(if continue_outer { 0 } else { 1 }, 23),
        ]),
        else_block: Block::default(),
    }));
    inner.push(write(loan, 20));
    outer.push(isolated(1, inner, vec![]));
    f.body = Body::Stmts(Block::new(vec![isolated(0, outer, vec![]), ret(None)]));
    with_choice(f)
}

#[test]
fn continuing_the_outer_loop_resolves_its_loop_local_owner() {
    require(source(true), &[(0, true, loop_group(1))], 0);
}

#[test]
fn continuing_the_inner_loop_does_not_resolve_the_live_outer_owner() {
    require(source(false), &[(0, false, loop_group(1))], 0);
}
