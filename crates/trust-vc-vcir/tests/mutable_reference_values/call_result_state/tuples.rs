// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Result slots retain their individual typed input owners.
use super::*;

fn source(wrong_second_resolution: bool) -> VcCrate {
    let carrier = reference(scalar());
    let pair_ty = Ty::Tuple(vec![carrier.clone(), carrier.clone()]);
    let mut target = function(pair_ty.clone());
    target.id = identity_id();
    target.name = "checked_owner_pair".into();
    let a = add(&mut target, carrier.clone(), Mode::Exec, LocalKind::Param);
    let b = add(&mut target, carrier.clone(), Mode::Exec, LocalKind::Param);
    target.ensures = vec![
        clause(eq(
            field(read(target.ret, pair_ty.clone()), 0),
            read(a, carrier.clone()),
        )),
        clause(eq(
            field(read(target.ret, pair_ty.clone()), 1),
            read(b, carrier.clone()),
        )),
    ];
    target.body = Body::Stmts(Block::new(vec![ret(Some(Expr::new(
        pair_ty.clone(),
        span(),
        ExprKind::Tuple(vec![read(a, carrier.clone()), read(b, carrier.clone())]),
    )))]));

    let mut f = function(Ty::Unit);
    let x = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let y = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let r = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let s = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let pair = add(&mut f, pair_ty.clone(), Mode::Exec, LocalKind::Let);
    let second_future = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let mut body = initial(x, r);
    body.extend(initial(y, s));
    body.push(stmt(StmtKind::Let {
        local: second_future,
        init: Some(future(read(s, carrier.clone()))),
    }));
    body.push(stmt(StmtKind::Let {
        local: pair,
        init: None,
    }));
    body.push(Stmt::new(
        SpanId(40),
        StmtKind::Call {
            callee: target.id,
            type_args: vec![],
            args: vec![read(r, carrier.clone()), read(s, carrier.clone())],
            dest: Some(Place::local(pair)),
            site: SiteId(2),
        },
    ));
    let first = resolved(field(read(pair, pair_ty.clone()), 0));
    let second = if wrong_second_resolution {
        resolved(field(read(pair, pair_ty.clone()), 1))
    } else {
        eq(
            future(field(read(pair, pair_ty.clone()), 1)),
            read(second_future, scalar()),
        )
    };
    body.push(assertion(
        Expr::binary(BinOp::And, first, second, Ty::Bool, span()),
        0,
    ));
    body.push(stmt(StmtKind::Assign {
        place: Place {
            local: pair,
            projections: vec![Projection::TupleField(1), Projection::Deref],
        },
        value: integer(11),
    }));
    body.push(assertion(
        Expr::binary(
            BinOp::And,
            eq(read(x, scalar()), integer(7)),
            eq(current(field(read(pair, pair_ty), 1)), integer(11)),
            Ty::Bool,
            span(),
        ),
        1,
    ));
    body.push(ret(None));
    f.body = Body::Stmts(Block::new(body));
    let mut source = krate(f);
    source.fns.push(target);
    source
}

#[test]
fn returned_tuple_slots_resolve_independently_and_preserve_their_typed_owners() {
    require(source(false), &[true, true]);
}

#[test]
fn mutating_one_returned_slot_refutes_its_early_resolution() {
    require(source(true), &[false, true]);
}
