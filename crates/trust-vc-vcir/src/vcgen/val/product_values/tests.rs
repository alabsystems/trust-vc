// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source-signature and value-layout controls, without a solver verdict.

use super::*;
use crate::{
    Body, DefHash, Expr, FieldDecl, FnAttrs, FnKind, FnRole, LocalDecl, LocalId, LocalKind, Mode,
    VariantDecl,
};

fn f(n: u64) -> FnId {
    FnId(DefHash::new(42, n))
}
fn a(n: u64) -> AdtId {
    AdtId(DefHash::new(42, n))
}
fn pair(inner: Ty) -> Ty {
    Ty::Adt(a(1), vec![inner])
}
fn signature(n: u64, ty: Ty) -> FnDecl {
    let local = |name: &str, kind| LocalDecl {
        name: name.into(),
        ty: ty.clone(),
        mode: Mode::Spec,
        prophecy: crate::DeclProphecy::Default,
        mutable: false,
        kind,
        span: SpanId(0),
    };
    FnDecl {
        id: f(n),
        name: format!("f{n}"),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec!["A".into()],
        locals: vec![
            local("result", LocalKind::Return),
            local("value", LocalKind::Param),
        ],
        params: vec![LocalId(1)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Spec(Expr::read(crate::Place::local(LocalId(1)), ty, SpanId(0))),
    }
}
fn source() -> VcCrate {
    let mut krate = VcCrate::new("formal product codec");
    krate.adts.push(AdtDecl {
        id: a(1),
        name: "Pair".into(),
        type_params: vec!["A".into()],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Pair".into(),
            fields: vec![
                FieldDecl {
                    name: "value".into(),
                    ty: Ty::Param(0),
                    mode: Mode::Exec,
                },
                FieldDecl {
                    name: "ready".into(),
                    ty: Ty::Bool,
                    mode: Mode::Exec,
                },
            ],
        }],
    });
    krate.fns.push(signature(1, Ty::Param(0)));
    krate.fns.push(signature(2, pair(Ty::Param(0))));
    let mut caller = signature(99, Ty::Unit);
    caller.type_params.clear();
    krate.fns.push(caller);
    krate
}
fn environments(ctx: &Ctx<'_>, callee: FnId, types: &[Ty]) -> (TypeEnv, TypeEnv) {
    let caller = TypeEnv::new(f(99), vec![]);
    let arguments = types
        .iter()
        .map(|ty| ctx.type_argument(ty, &caller, SpanId(0)).unwrap())
        .collect();
    (caller, TypeEnv::new(callee, arguments))
}
fn input() -> Val {
    Val::Node(vec![Val::Leaf(Term::Int(7)), Val::Leaf(Term::Bool(true))])
}
fn view<'a>(
    position: FormalPosition,
    actual_ty: &'a Ty,
    types: &'a [Ty],
    caller: &'a TypeEnv,
    callee: &'a TypeEnv,
) -> FormalValue<'a> {
    FormalValue {
        position,
        actual_ty,
        type_args: types,
        caller,
        callee,
        span: SpanId(0),
        work: None,
    }
}

#[test]
fn formal_parameter_and_formal_product_keep_distinct_abis() {
    let krate = source();
    assert!(crate::check_crate(&krate).is_empty());
    let ctx = Ctx::new(&krate);
    let ty = pair(Ty::int());
    let types = vec![ty.clone()];
    let (caller, callee) = environments(&ctx, f(1), &types);
    let shape = ctx
        .poly_shape(&Ty::Param(0), Some(f(1)), SpanId(0))
        .unwrap();
    let boxed = ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &ty,
                &types,
                &caller,
                &callee,
            ),
            &shape,
            input(),
        )
        .unwrap();
    assert!(
        matches!(&boxed, Val::Leaf(Term::Call { name, sort: Sort::Poly, .. }) if name.starts_with("pack_product"))
    );
    let result_shape = ctx.shape(&Ty::Param(0), Some(f(1)), SpanId(0)).unwrap();
    let decoded = ctx
        .formal_value(
            view(FormalPosition::Result, &ty, &types, &caller, &callee),
            &result_shape,
            boxed,
        )
        .unwrap();
    assert!(decoded.matches(&ctx.shape(&ty, caller.owner(), SpanId(0)).unwrap()));

    let ctx = Ctx::new(&krate);
    let types = vec![Ty::int()];
    let (caller, callee) = environments(&ctx, f(2), &types);
    let shape = ctx
        .poly_shape(&pair(Ty::Param(0)), Some(f(2)), SpanId(0))
        .unwrap();
    let boxed = ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &ty,
                &types,
                &caller,
                &callee,
            ),
            &shape,
            input(),
        )
        .unwrap();
    let Val::Node(fields) = boxed else {
        panic!("an explicit formal product keeps its field ABI");
    };
    assert_eq!(fields.len(), 2);
    assert!(fields
        .iter()
        .all(|field| matches!(field, Val::Leaf(value) if value.sort() == Sort::Poly)));
    assert!(ctx
        .type_functions()
        .iter()
        .all(|function| !function.name.starts_with("pack_product")));
    let result_shape = ctx
        .shape(&pair(Ty::Param(0)), Some(f(2)), SpanId(0))
        .unwrap();
    let result = Val::Node(vec![
        Val::Leaf(Term::var("result_value", Sort::Poly)),
        Val::Leaf(Term::Bool(true)),
    ]);
    assert!(ctx
        .formal_value(
            view(FormalPosition::Result, &ty, &types, &caller, &callee),
            &result_shape,
            result
        )
        .unwrap()
        .matches(&ctx.shape(&ty, caller.owner(), SpanId(0)).unwrap()));
}

#[test]
fn wrong_signature_nominal_order_and_decoration_refuse_before_coercion() {
    let mut krate = source();
    let mut other = krate.adts[0].clone();
    other.id = a(2);
    other.name = "Other".into();
    krate.adts.push(other);
    let ctx = Ctx::new(&krate);
    let ty = pair(Ty::int());
    let types = vec![ty.clone()];
    let (caller, callee) = environments(&ctx, f(1), &types);
    let shape = ctx
        .poly_shape(&Ty::Param(0), Some(f(1)), SpanId(0))
        .unwrap();
    let wrong_nominal = Ty::Adt(a(2), vec![Ty::int()]);
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &wrong_nominal,
                &types,
                &caller,
                &callee
            ),
            &shape,
            input()
        )
        .is_err());
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(1),
                &ty,
                &types,
                &caller,
                &callee
            ),
            &shape,
            input()
        )
        .is_err());
    assert!(ctx
        .formal_value(
            view(FormalPosition::SpecParameter(0), &ty, &[], &caller, &callee),
            &shape,
            input()
        )
        .is_err());
    let wrong_order = Val::Node(vec![Val::Leaf(Term::Bool(true)), Val::Leaf(Term::Int(7))]);
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &ty,
                &types,
                &caller,
                &callee
            ),
            &shape,
            wrong_order
        )
        .is_err());
    let borrowed = Ty::Ref {
        mutable: false,
        inner: Box::new(ty.clone()),
    };
    let borrowed_types = vec![borrowed.clone()];
    assert!(
        ctx.formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &borrowed,
                &borrowed_types,
                &caller,
                &callee
            ),
            &shape,
            input()
        )
        .is_err(),
        "equal underlying TypeIds do not erase a mismatching decoration vector"
    );
    let (caller, correct) = environments(&ctx, f(1), &borrowed_types);
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &borrowed,
                &borrowed_types,
                &caller,
                &correct
            ),
            &shape,
            input()
        )
        .is_ok());
}

#[test]
fn opaque_values_keep_their_scalar_bridge_and_cyclic_products_refuse() {
    let mut krate = source();
    krate.adts.push(AdtDecl {
        id: a(3),
        name: "Abstract".into(),
        type_params: vec![],
        span: SpanId(0),
        kind: AdtKind::Opaque,
        variants: vec![],
    });
    let ctx = Ctx::new(&krate);
    let ty = Ty::Adt(a(3), vec![]);
    let types = vec![ty.clone()];
    let (caller, callee) = environments(&ctx, f(1), &types);
    let shape = ctx
        .poly_shape(&Ty::Param(0), Some(f(1)), SpanId(0))
        .unwrap();
    let native = ctx.shape(&ty, caller.owner(), SpanId(0)).unwrap();
    let Shape::Leaf(leaf) = native else {
        panic!("opaque representation must remain a leaf");
    };
    let value = Val::Leaf(Term::var("abstract_value", leaf.sort()));
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &ty,
                &types,
                &caller,
                &callee
            ),
            &shape,
            value
        )
        .is_ok());
    assert!(ctx
        .type_functions()
        .iter()
        .all(|function| !function.name.starts_with("pack_product")
            && !function.name.starts_with("project_product")));
    drop(ctx);
    let bad = Ty::Adt(a(4), vec![]);
    krate.adts.push(AdtDecl {
        id: a(4),
        name: "Bad".into(),
        type_params: vec![],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Bad".into(),
            fields: vec![FieldDecl {
                name: "again".into(),
                ty: bad.clone(),
                mode: Mode::Exec,
            }],
        }],
    });
    let ctx = Ctx::new(&krate);
    let types = vec![bad.clone()];
    let (caller, callee) = environments(&ctx, f(1), &types);
    let shape = ctx
        .poly_shape(&Ty::Param(0), Some(f(1)), SpanId(0))
        .unwrap();
    assert!(ctx
        .formal_value(
            view(
                FormalPosition::SpecParameter(0),
                &bad,
                &types,
                &caller,
                &callee
            ),
            &shape,
            Val::Node(vec![])
        )
        .is_err());
}

#[test]
fn nested_and_zero_child_values_use_the_same_bounded_codec() {
    let mut krate = source();
    krate.adts.push(AdtDecl {
        id: a(5),
        name: "Empty".into(),
        type_params: vec!["A".into()],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Empty".into(),
            fields: vec![],
        }],
    });
    let ctx = Ctx::new(&krate);
    for (ty, value) in [
        (
            pair(pair(Ty::int())),
            Val::Node(vec![input(), Val::Leaf(Term::Bool(true))]),
        ),
        (Ty::Unit, Val::Node(vec![])),
        (Ty::Adt(a(5), vec![Ty::Bool]), Val::Node(vec![])),
    ] {
        let types = vec![ty.clone()];
        let (caller, callee) = environments(&ctx, f(1), &types);
        let shape = ctx
            .poly_shape(&Ty::Param(0), Some(f(1)), SpanId(0))
            .unwrap();
        let boxed = ctx
            .formal_value(
                view(
                    FormalPosition::SpecParameter(0),
                    &ty,
                    &types,
                    &caller,
                    &callee,
                ),
                &shape,
                value,
            )
            .unwrap();
        let result = ctx
            .formal_value(
                view(FormalPosition::Result, &ty, &types, &caller, &callee),
                &shape,
                boxed,
            )
            .unwrap();
        assert!(result.matches(&ctx.shape(&ty, caller.owner(), SpanId(0)).unwrap()));
    }
    let caller = TypeEnv::default();
    let callee = TypeEnv::default();
    let mut codec = Codec {
        ctx: &ctx,
        caller: &caller,
        callee: &callee,
        span: SpanId(0),
        left: 0,
        work: None,
    };
    assert!(codec
        .box_whole(&Ty::Unit, &Shape::Node(vec![]), Val::Node(vec![]))
        .is_err());
    assert_eq!(codec.left, 0);
}
