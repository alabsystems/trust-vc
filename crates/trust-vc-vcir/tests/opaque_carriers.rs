//! Abstract nominal values without a private representation or library axiom.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::solve::{self, Limits, Verdict};
use trust_vc_vcir::vcgen::{
    self,
    term::{Sort, Term},
    FnVcs,
};
use trust_vc_vcir::{
    check_crate, AdtDecl, AdtId, AdtKind, BinOp, Block, Body, ClauseAttrs, DefHash, Expr, ExprKind,
    FieldDecl, FnAttrs, FnDecl, FnId, FnKind, FnRole, IntRange, LocalDecl, LocalId, LocalKind,
    Mode, Place, SiteId, SpanId, Stmt, StmtKind, Ty, VariantDecl, VcCrate,
};

fn carrier(id: u64) -> AdtDecl {
    AdtDecl {
        id: AdtId(DefHash::new(1, id)),
        name: "same_display_name".into(),
        type_params: vec!["A".into()],
        span: SpanId(0),
        kind: AdtKind::Opaque,
        variants: vec![],
    }
}

fn value_type(id: u64, argument: Ty) -> Ty {
    Ty::Adt(AdtId(DefHash::new(1, id)), vec![argument])
}

fn read(id: u32, ty: Ty) -> Expr {
    Expr {
        span: SpanId(0),
        ty,
        kind: ExprKind::Read(Place::local(LocalId(id))),
    }
}

fn equal(left: Expr, right: Expr) -> Expr {
    Expr {
        span: SpanId(0),
        ty: Ty::Bool,
        kind: ExprKind::Binary {
            op: BinOp::Eq,
            lhs: Box::new(left),
            rhs: Box::new(right),
            check: None,
        },
    }
}

fn source(goal: Expr, left: Ty, right: Ty) -> VcCrate {
    let mut krate = VcCrate::new("opaque carrier controls");
    krate.adts = vec![carrier(1), carrier(2)];
    krate.fns.push(FnDecl {
        id: FnId(DefHash::new(1, 3)),
        name: "test".into(),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![
            LocalDecl {
                name: "return".into(),
                ty: Ty::Unit,
                mode: Mode::Spec,
                prophecy: trust_vc_vcir::DeclProphecy::Default,
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(0),
            },
            LocalDecl {
                name: "x".into(),
                ty: left,
                mode: Mode::Spec,
                prophecy: trust_vc_vcir::DeclProphecy::Default,
                mutable: false,
                kind: LocalKind::Param,
                span: SpanId(0),
            },
            LocalDecl {
                name: "y".into(),
                ty: right,
                mode: Mode::Spec,
                prophecy: trust_vc_vcir::DeclProphecy::Default,
                mutable: false,
                kind: LocalKind::Param,
                span: SpanId(0),
            },
        ],
        params: vec![LocalId(1), LocalId(2)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block {
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
        }),
    });
    krate
}

#[test]
fn opaque_equality_has_one_real_leaf_and_a_refuted_one_line_twin() {
    let ty = value_type(1, Ty::Bool);
    for (right, expected) in [(1, true), (2, false)] {
        let krate = source(
            equal(read(1, ty.clone()), read(right, ty.clone())),
            ty.clone(),
            ty.clone(),
        );
        assert!(check_crate(&krate).is_empty());
        let vcs = vcgen::generate(&krate);
        let FnVcs::Checks(checks) = &vcs.fns[0].1 else {
            panic!("carrier was refused: {vcs:?}");
        };
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].query.nominal_types, vec![ty.clone()]);
        assert!(checks[0]
            .query
            .symbols
            .iter()
            .any(|symbol| symbol.sort == Sort::Nominal(0)));
        let verdict = solve::check(&checks[0].query, "opaque equality", &Limits::default());
        assert!(
            if expected {
                matches!(verdict, Verdict::Proved { .. })
            } else {
                matches!(verdict, Verdict::Refuted { .. })
            },
            "{verdict:?}"
        );
    }
}

#[test]
fn opaque_registry_keeps_declaration_and_instantiation_identity() {
    for other in [
        value_type(2, Ty::Bool),
        value_type(1, Ty::Int(IntRange::U(8))),
    ] {
        let ty = value_type(1, Ty::Bool);
        let krate = source(
            equal(read(1, ty.clone()), read(1, ty.clone())),
            ty.clone(),
            other.clone(),
        );
        assert!(check_crate(&krate).is_empty());
        let vcs = vcgen::generate(&krate);
        let FnVcs::Checks(checks) = &vcs.fns[0].1 else {
            panic!("{vcs:?}");
        };
        assert_eq!(checks[0].query.nominal_types.len(), 2);
        assert!(checks[0].query.nominal_types.contains(&ty));
        assert!(checks[0].query.nominal_types.contains(&other));
    }
}

#[test]
fn opaque_constructor_and_field_projection_remain_malformed() {
    let ty = value_type(1, Ty::Bool);
    let construct = Expr {
        span: SpanId(0),
        ty: ty.clone(),
        kind: ExprKind::Ctor {
            adt: AdtId(DefHash::new(1, 1)),
            variant: 0,
            fields: vec![],
        },
    };
    let constructed = source(
        equal(read(1, ty.clone()), construct),
        ty.clone(),
        ty.clone(),
    );
    assert!(check_crate(&constructed)
        .iter()
        .any(|error| error.message.contains("constructor")));
    let field = Expr {
        span: SpanId(0),
        ty: Ty::Bool,
        kind: ExprKind::Field {
            base: Box::new(read(1, ty.clone())),
            variant: 0,
            field: 0,
        },
    };
    let projected = source(equal(field.clone(), field), ty.clone(), ty);
    assert!(check_crate(&projected)
        .iter()
        .any(|error| error.message.contains("field")));
}

#[test]
fn opaque_private_fields_cannot_be_smuggled_through_a_variant() {
    let ty = value_type(1, Ty::Bool);
    let mut krate = source(
        equal(read(1, ty.clone()), read(1, ty.clone())),
        ty.clone(),
        ty,
    );
    krate.adts[0].variants.push(VariantDecl {
        name: "hidden".into(),
        fields: vec![FieldDecl {
            name: "private".into(),
            ty: Ty::Bool,
            mode: Mode::Exec,
        }],
    });
    assert!(check_crate(&krate)
        .iter()
        .any(|error| error.message.contains("must not expose")));
    assert_eq!(krate.adts[0].field_ty(0, 0, &[Ty::Bool]), None);
}

#[test]
fn generic_carriers_use_typed_poly_without_a_generic_nominal_sort() {
    for other in [1, 2] {
        let ty = value_type(1, Ty::Param(0));
        let mut krate = source(
            equal(read(1, ty.clone()), read(other, ty.clone())),
            ty.clone(),
            ty,
        );
        krate.fns[0].type_params = vec!["A".into()];
        assert!(check_crate(&krate).is_empty());
        let vcs = vcgen::generate(&krate);
        let FnVcs::Checks(checks) = &vcs.fns[0].1 else {
            panic!("{vcs:?}");
        };
        let query = &checks[0].query;
        assert!(query.nominal_types.is_empty());
        assert!(query.symbols.iter().any(|symbol| symbol.sort == Sort::Poly));
        assert!(query
            .functions
            .iter()
            .any(|function| function.name == "has_type"
                && function.params == [Sort::Poly, Sort::TypeId]
                && function.ret == Sort::Bool));
        let verdict = solve::check(query, "generic opaque identity", &Limits::default());
        assert!(
            if other == 1 {
                matches!(verdict, Verdict::Proved { .. })
            } else {
                matches!(verdict, Verdict::Refuted { .. })
            },
            "{verdict:?}"
        );
    }
}

#[test]
fn malformed_nominal_query_registry_cannot_use_the_literal_true_shortcut() {
    let mut query = vcgen::Query {
        architectures: None,
        bitvector: None,
        nominal_types: vec![Ty::Bool],
        symbols: vec![],
        functions: vec![],
        definitions: vec![],
        hypotheses: vec![],
        goal: Term::Bool(true),
    };
    assert!(matches!(
        solve::check(&query, "malformed", &Limits::default()),
        Verdict::Error { .. }
    ));
    let ty = value_type(1, Ty::Bool);
    query.nominal_types = vec![ty.clone(), ty];
    assert!(matches!(
        solve::check(&query, "duplicate", &Limits::default()),
        Verdict::Error { .. }
    ));
}

#[test]
fn opaque_results_compose_with_spec_products_without_collapsing() {
    let ty = value_type(1, Ty::Bool);
    let result = Ty::Tuple(vec![ty.clone(), Ty::Int(IntRange::Nat)]);
    let id = FnId(DefHash::new(1, 4));
    for (right, expected) in [(1, true), (2, false)] {
        let call = Expr::new(
            result.clone(),
            SpanId(0),
            ExprKind::Call {
                callee: id,
                type_args: vec![],
                args: vec![read(1, ty.clone())],
            },
        );
        let projected = Expr::new(
            ty.clone(),
            SpanId(0),
            ExprKind::TupleField {
                base: Box::new(call),
                index: 0,
            },
        );
        let mut krate = source(
            equal(projected, read(right, ty.clone())),
            ty.clone(),
            ty.clone(),
        );
        let mut pair = krate.fns[0].clone();
        pair.id = id;
        pair.name = "opaque_and_nat".into();
        pair.mode = Mode::Spec;
        pair.locals.truncate(2);
        pair.locals[0].ty = result.clone();
        pair.params = vec![LocalId(1)];
        pair.body = Body::Spec(Expr::new(
            result.clone(),
            SpanId(0),
            ExprKind::Tuple(vec![
                read(1, ty.clone()),
                Expr::int_lit(0, Ty::Int(IntRange::Nat), SpanId(0)),
            ]),
        ));
        krate.fns.insert(0, pair);
        assert!(check_crate(&krate).is_empty());
        let vcs = vcgen::generate(&krate);
        let (_, FnVcs::Checks(checks)) = vcs
            .fns
            .iter()
            .find(|(id, _)| *id == FnId(DefHash::new(1, 3)))
            .unwrap()
        else {
            panic!("{vcs:?}");
        };
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].query.nominal_types, vec![ty.clone()]);
        assert!(checks[0]
            .query
            .functions
            .iter()
            .any(|f| f.ret == Sort::Nominal(0)));
        assert!(checks[0].query.functions.iter().any(|f| f.ret == Sort::Int));
        let verdict = solve::check(&checks[0].query, "opaque product", &Limits::default());
        assert!(
            if expected {
                matches!(verdict, Verdict::Proved { .. })
            } else {
                matches!(verdict, Verdict::Refuted { .. })
            },
            "{verdict:?}"
        );
    }
}
