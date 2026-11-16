// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A nonowned expression result does not erase its nested affine transfers.
use super::helpers::*;
use super::*;

fn reference() -> Ty {
    Ty::MutRef(Box::new(scalar()))
}
fn integer(value: i128) -> Expr {
    Expr::int_lit(value, scalar(), span())
}

fn moving_scalar(bound: LocalId, input: LocalId, value: i128) -> Expr {
    Expr::new(
        scalar(),
        span(),
        ExprKind::Let {
            local: bound,
            value: Box::new(read(input, reference())),
            body: Box::new(integer(value)),
        },
    )
}

fn require_moved(f: FnDecl, detail: &str, at: SpanId) {
    let id = f.id;
    assert_eq!(f.mode, Mode::Exec);
    assert_eq!(f.role, FnRole::Item);
    assert!(f.type_params.is_empty() && f.attrs.instance.is_none());
    assert!(!f.attrs.external_body);
    let mut source = VcCrate::new("nonowned results retain affine effects");
    source.fns.push(f);
    // This must be accepted by the public type, value-mode and prophecy
    // checks before the real ownership generator refuses its illegal move.
    let generated = generate(&source);
    assert_eq!(generated.fns.len(), 1);
    let Some(FnVcs::Refused(problem)) = generated.get(id) else {
        panic!("the nested move must not become a supported body: {generated:?}");
    };
    assert_eq!(problem.tag, "mut-ref-moved");
    assert_eq!(problem.detail, detail);
    assert_eq!(problem.span, at);
}

#[test]
fn a_scalar_let_result_still_moves_its_nested_reference_value() {
    let mut f = function(1008, Ty::Unit);
    let input = add(&mut f, reference(), Mode::Exec, LocalKind::Param);
    let bound = add(&mut f, reference(), Mode::Exec, LocalKind::Bound);
    let result = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let write = SpanId(21);
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: result,
            init: Some(moving_scalar(bound, input, 0)),
        }),
        Stmt::new(
            write,
            StmtKind::Assign {
                place: Place::deref(input),
                value: integer(7),
            },
        ),
        ret(None),
    ]));
    require_moved(f, "write through a moved reference", write);
}

#[test]
fn scalar_tuple_results_reject_two_nested_moves_before_any_join_or_later_use() {
    let mut f = function(1009, Ty::Unit);
    let input = add(&mut f, reference(), Mode::Exec, LocalKind::Param);
    let first = add(&mut f, reference(), Mode::Exec, LocalKind::Bound);
    let second = add(&mut f, reference(), Mode::Exec, LocalKind::Bound);
    let ty = Ty::Tuple(vec![scalar(), scalar()]);
    let result = add(&mut f, ty.clone(), Mode::Exec, LocalKind::Let);
    let tuple = SpanId(31);
    let value = Expr::new(
        ty,
        tuple,
        ExprKind::Tuple(vec![
            moving_scalar(first, input, 0),
            moving_scalar(second, input, 1),
        ]),
    );
    // The only later statement is return. The duplicate is detected while
    // consuming this one initializer, without a CFG join or later use.
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: result,
            init: Some(value),
        }),
        ret(None),
    ]));
    require_moved(f, "access to moved owned reference storage", tuple);
}
