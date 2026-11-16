// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A specialized predicate must preserve its body before contracts may share it.

use super::*;

fn value(ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(1)), ty, span())
}

fn predicate_body(ty: Ty) -> Expr {
    Expr::binary(BinOp::Eq, value(ty.clone()), value(ty), Ty::Bool, span())
}

fn invocation(callee: FnId, type_args: Vec<Ty>, ty: Ty) -> Expr {
    Expr::new(
        Ty::Bool,
        SpanId(80),
        ExprKind::Call {
            callee,
            type_args,
            args: vec![value(ty)],
        },
    )
}

fn source() -> VcCrate {
    let mut predicate = function(20);
    predicate.mode = Mode::Spec;
    predicate.type_params = vec!["T".into()];
    predicate.locals[0].ty = Ty::Bool;
    predicate.locals[1].ty = Ty::Param(0);
    for local in &mut predicate.locals {
        local.mode = Mode::Spec;
        local.mutable = false;
    }
    predicate.body = Body::Spec(predicate_body(Ty::Param(0)));
    let mut specialized = predicate.clone();
    specialized.id = id(21);
    specialized.name = "predicate_u64".into();
    specialized.role = FnRole::Instance;
    specialized.type_params.clear();
    specialized.locals[1].ty = Ty::uint(64);
    specialized.body = Body::Spec(predicate_body(Ty::uint(64)));
    specialized.attrs.instance = Some(GenericInstance {
        declaration: predicate.id,
        type_args: vec![Ty::uint(64)],
    });

    let mut outer = function(10);
    outer.type_params = vec!["T".into()];
    outer.locals[1].ty = Ty::Param(0);
    outer.unwind = Some(UnwindSpec::NoUnwindWhen(invocation(
        predicate.id,
        vec![Ty::Param(0)],
        Ty::Param(0),
    )));
    let mut instance = outer.clone();
    instance.id = id(11);
    instance.name = "outer_u64".into();
    instance.span = SpanId(11);
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    instance.locals[1].ty = Ty::uint(64);
    instance.unwind = Some(UnwindSpec::NoUnwindWhen(invocation(
        specialized.id,
        vec![],
        Ty::uint(64),
    )));
    instance.attrs.instance = Some(GenericInstance {
        declaration: outer.id,
        type_args: vec![Ty::uint(64)],
    });
    let mut source = VcCrate::new("canonical unwind predicate dependency");
    source.fns = vec![outer, instance, predicate, specialized];
    source
}

#[test]
fn an_unwind_instance_can_use_a_canonical_specialized_spec_predicate() {
    let source = source();
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    let original = &source.fns[0];
    let instance = &source.fns[1];
    let predicate = &source.fns[2];
    let specialized = &source.fns[3];
    assert_eq!(
        (original.id, instance.id, predicate.id, specialized.id),
        (id(10), id(11), id(20), id(21))
    );
    assert_eq!(specialized.role, FnRole::Instance);
    assert_eq!(
        specialized.attrs.instance.as_ref().unwrap().declaration,
        predicate.id
    );
    assert_eq!(
        specialized.attrs.instance.as_ref().unwrap().type_args,
        vec![Ty::uint(64)]
    );
    assert_eq!(predicate.locals[1].ty, Ty::Param(0));
    assert_eq!(specialized.locals[1].ty, Ty::uint(64));
    let Some(UnwindSpec::NoUnwindWhen(condition)) = &original.unwind else {
        unreachable!()
    };
    assert!(
        matches!(&condition.kind, ExprKind::Call { callee, type_args, .. }
        if *callee == predicate.id && *type_args == vec![Ty::Param(0)])
    );
    let Some(UnwindSpec::NoUnwindWhen(condition)) = &instance.unwind else {
        unreachable!()
    };
    assert!(
        matches!(&condition.kind, ExprKind::Call { callee, type_args, .. }
        if *callee == specialized.id && type_args.is_empty())
    );
}

#[test]
fn a_changed_predicate_instance_body_invalidates_the_outer_unwind_contract() {
    let mut source = source();
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    let Body::Spec(body) = &source.fns[3].body else {
        unreachable!()
    };
    source.fns[3].body = Body::Spec(not(body.clone()));
    assert_eq!(
        check_crate(&source),
        vec![WfError {
            class: WfClass::Malformed,
            function: Some(id(11)),
            span: SpanId(11),
            message: "in `outer_u64`: an instance signature disagrees with its native origin"
                .into(),
        }]
    );
}
