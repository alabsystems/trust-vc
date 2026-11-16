// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::helpers::*;
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, QueryGroup};

fn reference() -> Ty {
    Ty::MutRef(Box::new(scalar()))
}
fn integer(value: i128) -> Expr {
    Expr::int_lit(value, scalar(), span())
}
fn equality(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinOp::Eq, a, b, Ty::Bool, span())
}
fn assertion(expr: Expr) -> Stmt {
    stmt(StmtKind::Assert {
        expr,
        site: SiteId(0),
        attrs: ClauseAttrs::default(),
    })
}
fn wrapper(mode: Mode) -> AdtDecl {
    AdtDecl {
        id: adt(100),
        name: "Wrapper".into(),
        type_params: vec!["T".into()],
        span: span(),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Wrapper".into(),
            fields: vec![FieldDecl {
                name: "value".into(),
                ty: Ty::Param(0),
                mode,
            }],
        }],
    }
}
fn wrapped(ty: Ty) -> Ty {
    Ty::Adt(adt(100), vec![ty])
}
fn field(local: LocalId, ty: Ty) -> Expr {
    Expr::new(
        ty.clone(),
        span(),
        ExprKind::Field {
            base: Box::new(read(local, wrapped(ty))),
            variant: 0,
            field: 0,
        },
    )
}
fn resolved(value: Expr) -> Expr {
    Expr::new(Ty::Bool, span(), ExprKind::HasResolved(Box::new(value)))
}
fn require(source: VcCrate, proved: bool) {
    let generated = generate(&source);
    for function in &source.fns {
        let Some(FnVcs::Checks(checks)) = generated.get(function.id) else {
            panic!("an original body must generate actual checks: {generated:?}");
        };
        assert_eq!(checks.len(), 1, "{checks:?}");
        let check = &checks[0];
        assert_eq!(check.site, SiteId(0));
        assert_eq!(check.group, QueryGroup::Body);
        assert_eq!(
            check.kind,
            CheckKind::Assert {
                span: span(),
                attrs: ClauseAttrs::default()
            }
        );
        assert!(!check.approximate && !check.order_unknown);
        assert!(check.query.architectures.is_none() && check.query.bitvector.is_none());
        assert!(
            !matches!(check.query.goal, Term::Bool(_)),
            "the query must reach AY: {check:?}"
        );
        let answer = check_detailed(&check.query, "ownership classification", &Limits::default());
        assert!(
            matches!(
                (&answer.verdict, proved),
                (Verdict::Proved { .. }, true) | (Verdict::Refuted { .. }, false)
            ),
            "expected proved={proved}: {answer:?}; check={check:?}"
        );
    }
}

#[test]
fn generic_ownership_uses_each_actual_argument_after_a_scalar_instantiation() {
    for expected in [7, 8] {
        let mut f = function(1003, Ty::Unit);
        add(&mut f, wrapped(scalar()), Mode::Exec, LocalKind::Let);
        let input = add(&mut f, wrapped(reference()), Mode::Exec, LocalKind::Param);
        let value = field(input, reference());
        let future = Expr::new(scalar(), span(), ExprKind::MutRefFuture(Box::new(value)));
        f.body = Body::Stmts(Block::new(vec![
            stmt(StmtKind::Assign {
                place: Place {
                    local: input,
                    projections: vec![
                        Projection::Field {
                            variant: 0,
                            field: 0,
                        },
                        Projection::Deref,
                    ],
                },
                value: integer(7),
            }),
            assertion(equality(future, integer(expected))),
            ret(None),
        ]));
        require(source(f, vec![wrapper(Mode::Exec)]), expected == 7);
    }
}

#[test]
fn spec_fields_remain_snapshots_while_proof_fields_are_owned() {
    for mode in [Mode::Spec, Mode::Proof] {
        let mut f = function(1004, Ty::Unit);
        let input = add(&mut f, wrapped(reference()), Mode::Exec, LocalKind::Param);
        f.body = Body::Stmts(Block::new(vec![
            assertion(resolved(field(input, reference()))),
            ret(None),
        ]));
        require(source(f, vec![wrapper(mode)]), mode == Mode::Proof);
    }
}

#[test]
fn a_future_move_of_a_proof_field_blocks_early_resolution() {
    let mut f = function(1005, Ty::Unit);
    let input = add(&mut f, wrapped(reference()), Mode::Exec, LocalKind::Param);
    let moved = add(&mut f, reference(), Mode::Proof, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        assertion(resolved(field(input, reference()))),
        stmt(StmtKind::Ghost(Block::new(vec![stmt(StmtKind::Let {
            local: moved,
            init: Some(field(input, reference())),
        })]))),
        ret(None),
    ]));
    require(source(f, vec![wrapper(Mode::Proof)]), false);
}

#[test]
fn shared_references_do_not_resolve_the_owned_reference_they_observe() {
    let mut f = function(1006, Ty::Unit);
    let input = add(
        &mut f,
        Ty::Ref {
            mutable: false,
            inner: Box::new(reference()),
        },
        Mode::Exec,
        LocalKind::Param,
    );
    f.body = Body::Stmts(Block::new(vec![
        assertion(resolved(Expr::read(
            Place::deref(input),
            reference(),
            span(),
        ))),
        ret(None),
    ]));
    require(source(f, vec![]), false);
}

#[test]
fn no_owned_loop_breaks_preserve_the_following_assertion() {
    for proved in [true, false] {
        let mut f = function(1007, Ty::Unit);
        let flag = add(&mut f, Ty::Bool, Mode::Exec, LocalKind::Param);
        f.requires.push(Clause {
            expr: read(flag, Ty::Bool),
            attrs: ClauseAttrs::default(),
            span: span(),
        });
        let condition = if proved {
            read(flag, Ty::Bool)
        } else {
            Expr::new(
                Ty::Bool,
                span(),
                ExprKind::Unary {
                    op: UnOp::Not,
                    arg: Box::new(read(flag, Ty::Bool)),
                    check: None,
                },
            )
        };
        f.body = Body::Stmts(Block::new(vec![
            stmt(StmtKind::Loop(Box::new(Loop {
                id: LoopId(0),
                isolation: true,
                allow_complex_invariants: false,
                cond: None,
                invariants: vec![],
                decreases: vec![],
                body: Block::new(vec![stmt(StmtKind::Break {
                    target: LoopId(0),
                    site: SiteId(13),
                })]),
                sites: LoopSites {
                    entry: SiteId(10),
                    end: SiteId(11),
                    exit: SiteId(12),
                },
            }))),
            assertion(condition),
            ret(None),
        ]));
        require(source(f, vec![]), proved);
    }
}
