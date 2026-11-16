// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An opaque call result is not a complete cover of another branch's pointees.
use super::*;

fn identity_id() -> FnId {
    FnId(DefHash::new(133, 3))
}

fn source(snapshot_storage: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Param);
    let x = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let y = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let z = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let r = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let r2 = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let s = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let proxy_ty = reference(reference(scalar()));
    let q = add(&mut f, proxy_ty.clone(), Mode::Exec, LocalKind::Let);
    let incoming = add(&mut f, proxy_ty.clone(), Mode::Exec, LocalKind::Let);
    let snapshot = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let mut statements = initial(x, r);
    statements.extend(initial(y, s));
    statements.extend(initial(z, r2));
    statements.push(stmt(StmtKind::Block(Block::new(vec![
        stmt(StmtKind::Let {
            local: q,
            init: None,
        }),
        stmt(StmtKind::If {
            cond: read(flag, Ty::Bool),
            then_block: Block::new(vec![
                stmt(StmtKind::Let {
                    local: incoming,
                    init: None,
                }),
                stmt(StmtKind::BorrowMut {
                    dest: incoming,
                    place: Place::local(r2),
                }),
                stmt(StmtKind::Call {
                    callee: identity_id(),
                    type_args: vec![],
                    args: vec![read(incoming, proxy_ty.clone())],
                    dest: Some(Place::local(q)),
                    site: SiteId(2),
                }),
            ]),
            else_block: Block::new(vec![stmt(StmtKind::BorrowMut {
                dest: q,
                place: Place::local(r),
            })]),
        }),
        stmt(StmtKind::Assign {
            place: Place::deref(q),
            value: read(s, reference(scalar())),
        }),
    ]))));
    statements.push(isolated(0, vec![leave(0, 13)], vec![]));
    if snapshot_storage {
        statements.push(stmt(StmtKind::Let {
            local: snapshot,
            init: Some(read(x, scalar())),
        }));
    }
    statements.push(write(r, 5));
    statements.push(assertion(
        if snapshot_storage {
            // On the true branch q points to r2, so x is still borrowed by r
            // and this premature snapshot was physically zero, not five.
            eq(read(snapshot, scalar()), integer(5))
        } else {
            eq(current(read(r, reference(scalar()))), integer(5))
        },
        0,
    ));
    statements.push(ret(None));
    f.body = Body::Stmts(Block::new(statements));

    // A checked executable identity, not a trusted declaration. The modular
    // signature has no result-alias postcondition, so its output is unknown.
    let mut identity = function(proxy_ty.clone());
    identity.id = identity_id();
    identity.name = "opaque_result_identity".into();
    let parameter = add(
        &mut identity,
        proxy_ty.clone(),
        Mode::Exec,
        LocalKind::Param,
    );
    identity.body = Body::Stmts(Block::new(vec![ret(Some(read(parameter, proxy_ty)))]));
    let mut source = krate(f);
    source.fns.push(identity);
    source
}

#[test]
fn joining_a_known_proxy_with_an_unknown_call_result_preserves_the_old_loan() {
    require_refusal(source(true), "mut-ref-borrowed");
}

#[test]
fn an_unknown_proxy_alternative_does_not_block_valid_parent_carrier_use() {
    require(source(false), &[(0, true, QueryGroup::Body)], 0);
}
