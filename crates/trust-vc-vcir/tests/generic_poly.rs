//! Boxed generic values and declaration-guarded result typing.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::solve::{self, Limits, Verdict};
use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

fn id(value: u64) -> FnId {
    FnId(DefHash::new(8, value))
}
fn carrier() -> Ty {
    Ty::Adt(AdtId(DefHash::new(8, 1)), vec![Ty::Param(0)])
}
fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}
fn nat(value: i128) -> Expr {
    Expr::int_lit(value, Ty::nat(), SpanId(0))
}
fn binary(op: BinOp, left: Expr, right: Expr, ty: Ty) -> Expr {
    Expr::binary(op, left, right, ty, SpanId(0))
}

fn function(number: u64, parameters: Vec<Ty>, result: Ty) -> FnDecl {
    let mut locals = vec![LocalDecl {
        name: "result".into(),
        ty: result,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: false,
        kind: LocalKind::Return,
        span: SpanId(0),
    }];
    for (index, ty) in parameters.iter().enumerate() {
        locals.push(LocalDecl {
            name: format!("p{index}"),
            ty: ty.clone(),
            mode: Mode::Spec,
            prophecy: trust_vc_vcir::DeclProphecy::Default,
            mutable: false,
            kind: LocalKind::Param,
            span: SpanId(0),
        });
    }
    FnDecl {
        id: id(number),
        name: format!("f{number}"),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec!["A".into()],
        locals,
        params: (1..=parameters.len())
            .map(|index| LocalId(u32::try_from(index).unwrap()))
            .collect(),
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}

fn call(callee: u64, type_args: Vec<Ty>, args: Vec<Expr>, ty: Ty) -> Expr {
    Expr::new(
        ty,
        SpanId(0),
        ExprKind::Call {
            callee: id(callee),
            type_args,
            args,
        },
    )
}

fn source() -> VcCrate {
    let mut krate = VcCrate::new("abstract typed values");
    krate.adts.push(AdtDecl {
        id: AdtId(DefHash::new(8, 1)),
        name: "Abstract".into(),
        type_params: vec!["A".into()],
        span: SpanId(0),
        kind: AdtKind::Opaque,
        variants: vec![],
    });
    krate
}

fn client(goal: Expr, parameters: Vec<Ty>, type_parameters: usize) -> FnDecl {
    let mut client = function(99, parameters, Ty::Unit);
    client.mode = Mode::Proof;
    client.type_params = (0..type_parameters)
        .map(|index| format!("T{index}"))
        .collect();
    client.body = Body::Stmts(Block {
        stmts: vec![
            Stmt {
                span: SpanId(0),
                kind: StmtKind::Assert {
                    expr: goal,
                    site: SiteId(0),
                    attrs: ClauseAttrs::default(),
                },
            },
            Stmt {
                span: SpanId(0),
                kind: StmtKind::Return {
                    value: None,
                    site: SiteId(1),
                },
            },
        ],
    });
    client
}

fn verdict(krate: &VcCrate) -> Verdict {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let vcs = vcgen::generate(krate);
    let (_, FnVcs::Checks(checks)) = vcs
        .fns
        .iter()
        .find(|(function, _)| *function == id(99))
        .unwrap()
    else {
        panic!("{vcs:?}");
    };
    assert_eq!(checks.len(), 1);
    solve::check(&checks[0].query, "generic typed values", &Limits::default())
}

#[test]
fn generic_opaque_nat_result_keeps_distinct_values() {
    for liar in [false, true] {
        let mut krate = source();
        krate.fns.push(function(1, vec![carrier()], Ty::nat()));
        let left = call(1, vec![Ty::Param(0)], vec![read(1, carrier())], Ty::nat());
        let goal = if liar {
            let right = call(1, vec![Ty::Param(0)], vec![read(2, carrier())], Ty::nat());
            binary(BinOp::Eq, left, right, Ty::Bool)
        } else {
            binary(BinOp::Ge, left, nat(0), Ty::Bool)
        };
        krate.fns.push(client(goal, vec![carrier(), carrier()], 1));
        let result = verdict(&krate);
        assert!(
            if liar {
                matches!(result, Verdict::Refuted { .. })
            } else {
                matches!(result, Verdict::Proved { .. })
            },
            "{result:?}"
        );
    }
}

#[test]
fn generic_type_arguments_do_not_share_an_uninterpreted_call() {
    for other in [0, 1] {
        let mut krate = source();
        krate.fns.push(function(1, vec![], Ty::nat()));
        let left = call(1, vec![Ty::Param(0)], vec![], Ty::nat());
        let right = call(1, vec![Ty::Param(other)], vec![], Ty::nat());
        krate
            .fns
            .push(client(binary(BinOp::Eq, left, right, Ty::Bool), vec![], 2));
        let result = verdict(&krate);
        assert!(
            if other == 0 {
                matches!(result, Verdict::Proved { .. })
            } else {
                matches!(result, Verdict::Refuted { .. })
            },
            "{result:?}"
        );
    }
}

fn product() -> Ty {
    Ty::Tuple(vec![Ty::nat(), carrier()])
}
fn second(value: Expr) -> Expr {
    Expr::new(
        carrier(),
        SpanId(0),
        ExprKind::TupleField {
            base: Box::new(value),
            index: 1,
        },
    )
}

fn recursive_pair() -> FnDecl {
    let mut function = function(2, vec![Ty::nat(), carrier()], product());
    let n = read(1, Ty::nat());
    let s = read(2, carrier());
    let argument =
        binary(BinOp::Sub, n.clone(), nat(1), Ty::int()).cast(CastKind::As, Ty::nat(), SpanId(0));
    let child = call(2, vec![Ty::Param(0)], vec![argument, s.clone()], product());
    let measured = call(
        1,
        vec![Ty::Param(0)],
        vec![second(child.clone())],
        Ty::nat(),
    );
    let step = Expr::new(
        product(),
        SpanId(0),
        ExprKind::Tuple(vec![
            binary(BinOp::Add, measured, nat(1), Ty::nat()),
            second(child),
        ]),
    );
    let base = Expr::new(product(), SpanId(0), ExprKind::Tuple(vec![nat(0), s]));
    function.body = Body::Spec(Expr::new(
        product(),
        SpanId(0),
        ExprKind::If {
            cond: Box::new(binary(BinOp::Eq, n.clone(), nat(0), Ty::Bool)),
            then_expr: Box::new(base),
            else_expr: Box::new(step),
        },
    ));
    function.decreases = vec![n.clone()];
    function.decreases_when = Some(binary(BinOp::Gt, n, nat(0), Ty::Bool));
    function
}

#[test]
fn zero_fuel_boxed_sibling_typing_does_not_require_its_body_guard() {
    for threshold in [0, 1] {
        let mut krate = source();
        krate.fns.push(function(1, vec![carrier()], Ty::nat()));
        krate.fns.push(recursive_pair());
        krate.rec_groups.push(RecGroup {
            members: vec![(id(2), 1)],
        });
        let value = call(
            2,
            vec![Ty::Param(0)],
            vec![nat(1), read(1, carrier())],
            product(),
        );
        let first = Expr::new(
            Ty::nat(),
            SpanId(0),
            ExprKind::TupleField {
                base: Box::new(value),
                index: 0,
            },
        );
        krate.fns.push(client(
            binary(BinOp::Gt, first, nat(threshold), Ty::Bool),
            vec![carrier()],
            1,
        ));
        let result = verdict(&krate);
        assert!(
            if threshold == 0 {
                matches!(result, Verdict::Proved { .. })
            } else {
                matches!(result, Verdict::Refuted { .. })
            },
            "{result:?}"
        );
    }
}
