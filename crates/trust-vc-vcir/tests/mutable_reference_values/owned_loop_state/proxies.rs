// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dropping a proxy must not discard a loan stored through its dereference.
use super::*;

fn source(later_write: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let x = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let y = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let r = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let s = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let proxy = add(
        &mut f,
        reference(reference(scalar())),
        Mode::Exec,
        LocalKind::Let,
    );
    let snapshot = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let mut statements = initial(x, r);
    statements.extend(initial(y, s));
    statements.push(stmt(StmtKind::Block(Block::new(vec![
        stmt(StmtKind::Let {
            local: proxy,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: proxy,
            place: Place::local(r),
        }),
        stmt(StmtKind::Assign {
            place: Place::deref(proxy),
            value: read(s, reference(scalar())),
        }),
    ]))));
    statements.push(isolated(0, vec![leave(0, 13)], vec![]));
    statements.push(stmt(StmtKind::Let {
        local: snapshot,
        init: Some(read(y, scalar())),
    }));
    if later_write {
        statements.push(write(r, 5));
    }
    // A permitted current snapshot is zero. Early future writeback must not
    // turn this into a proof of five by losing y's live loan at the cut.
    statements.push(assertion(
        eq(
            read(snapshot, scalar()),
            integer(if later_write { 5 } else { 0 }),
        ),
        0,
    ));
    statements.push(ret(None));
    f.body = Body::Stmts(Block::new(statements));
    krate(f)
}

#[test]
fn a_proxy_scope_cannot_hide_the_live_loan_written_to_its_parent_storage() {
    require_refusal(source(true), "mut-ref-borrowed");
}

#[test]
fn a_proxy_stored_loan_can_resolve_without_a_later_parent_mutation() {
    require(source(false), &[(0, true, QueryGroup::Body)], 0);
}
