//! Finite sums: real value/variant laws and deliberately false value twins.
//!
//! These are public IR controls, not native vstd or imported-body evidence.

use trust_vc_vcir::solve::{self, Limits, Verdict};
use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

fn adt(n: u64) -> AdtId {
    AdtId(DefHash::new(73, n))
}
fn fid() -> FnId {
    FnId(DefHash::new(73, 99))
}
fn sum(n: u64, argument: Ty) -> Ty {
    Ty::Adt(adt(n), vec![argument])
}
fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}
fn number(value: i128, ty: Ty) -> Expr {
    Expr::int_lit(value, ty, SpanId(0))
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinOp::Eq, left, right, Ty::Bool, SpanId(0))
}
fn ctor(n: u64, argument: Ty, variant: u32, fields: Vec<Expr>) -> Expr {
    Expr::new(
        sum(n, argument),
        SpanId(0),
        ExprKind::Ctor {
            adt: adt(n),
            variant,
            fields,
        },
    )
}
fn project(base: Expr, ty: Ty) -> Expr {
    Expr::new(
        ty,
        SpanId(0),
        ExprKind::Field {
            base: Box::new(base),
            variant: 1,
            field: 0,
        },
    )
}
fn test(base: Expr, variant: u32) -> Expr {
    Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::IsVariant {
            base: Box::new(base),
            variant,
        },
    )
}
fn clause(expr: Expr) -> Clause {
    Clause {
        expr,
        span: SpanId(0),
        attrs: ClauseAttrs::default(),
    }
}
fn declaration(n: u64) -> AdtDecl {
    AdtDecl {
        id: adt(n),
        name: "same_display_name".into(),
        type_params: vec!["V".into()],
        span: SpanId(0),
        kind: AdtKind::Enum,
        variants: vec![
            VariantDecl {
                name: "Empty".into(),
                fields: vec![],
            },
            VariantDecl {
                name: "Payload".into(),
                fields: vec![FieldDecl {
                    name: "value".into(),
                    ty: Ty::Param(0),
                    mode: Mode::Exec,
                }],
            },
        ],
    }
}
fn source(goal: Expr, params: Vec<Ty>, type_params: usize) -> VcCrate {
    let mut krate = VcCrate::new("finite sum controls");
    krate.adts.push(declaration(1));
    let mut locals = vec![LocalDecl {
        name: "result".into(),
        ty: Ty::Unit,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: false,
        kind: LocalKind::Return,
        span: SpanId(0),
    }];
    for (index, ty) in params.iter().enumerate() {
        locals.push(LocalDecl {
            name: format!("x{index}"),
            ty: ty.clone(),
            mode: Mode::Spec,
            prophecy: trust_vc_vcir::DeclProphecy::Default,
            mutable: false,
            kind: LocalKind::Param,
            span: SpanId(0),
        });
    }
    krate.fns.push(FnDecl {
        id: fid(),
        name: "client".into(),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: (0..type_params).map(|i| format!("T{i}")).collect(),
        locals,
        params: (1..=params.len()).map(|i| LocalId(i as u32)).collect(),
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::new(vec![
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
        ])),
    });
    krate
}
fn verdict(krate: &VcCrate, proved: bool) {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let generated = vcgen::generate(krate);
    let Some(FnVcs::Checks(checks)) = generated.get(fid()) else {
        panic!("{generated:?}");
    };
    assert_eq!(checks.len(), 1);
    let result = solve::check(&checks[0].query, "finite sum", &Limits::default());
    assert!(
        if proved {
            matches!(result, Verdict::Proved { .. })
        } else {
            matches!(result, Verdict::Refuted { .. })
        },
        "{result:?}"
    );
}

#[test]
fn concrete_sum_payload_round_trip_and_false_twin() {
    let ty = Ty::Int(IntRange::U(8));
    for liar in [false, true] {
        let value = ctor(1, ty.clone(), 1, vec![number(3, ty.clone())]);
        verdict(
            &source(
                eq(
                    project(value, ty.clone()),
                    number(if liar { 4 } else { 3 }, ty.clone()),
                ),
                vec![],
                0,
            ),
            !liar,
        );
    }
}

#[test]
fn generic_payload_projection_keeps_its_actual_value() {
    for liar in [false, true] {
        let ty = Ty::Param(0);
        let value = ctor(1, ty.clone(), 1, vec![read(1, ty.clone())]);
        verdict(
            &source(
                eq(
                    project(value, ty.clone()),
                    read(if liar { 2 } else { 1 }, ty.clone()),
                ),
                vec![ty.clone(), ty],
                1,
            ),
            !liar,
        );
    }
}

#[test]
fn variant_tests_exhaustiveness_and_constructor_disjointness() {
    let ty = Ty::Bool;
    let payload = ctor(1, ty.clone(), 1, vec![Expr::bool_lit(true, SpanId(0))]);
    let empty = ctor(1, ty.clone(), 0, vec![]);
    verdict(&source(test(payload.clone(), 1), vec![], 0), true);
    verdict(&source(test(payload.clone(), 0), vec![], 0), false);
    verdict(&source(eq(payload, empty), vec![], 0), false);
    let value = read(1, sum(1, ty.clone()));
    let either = Expr::binary(
        BinOp::Or,
        test(value.clone(), 0),
        test(value, 1),
        Ty::Bool,
        SpanId(0),
    );
    verdict(&source(either, vec![sum(1, ty)], 0), true);
}

#[test]
fn wrong_variant_selector_and_equal_display_names_add_no_value_equation() {
    let ty = Ty::Int(IntRange::U(8));
    let value = project(ctor(1, ty.clone(), 0, vec![]), ty.clone());
    verdict(
        &source(eq(value.clone(), number(0, ty.clone())), vec![], 0),
        false,
    );
    let mut krate = source(
        eq(value, project(ctor(2, ty.clone(), 0, vec![]), ty)),
        vec![],
        0,
    );
    krate.adts.push(declaration(2));
    verdict(&krate, false);
}

#[test]
fn empty_payloads_at_different_type_arguments_do_not_share_selectors() {
    let small = Ty::Int(IntRange::U(8));
    let wide = Ty::Int(IntRange::U(16));
    let first = project(ctor(1, small.clone(), 0, vec![]), small.clone());
    let second = project(ctor(1, wide.clone(), 0, vec![]), wide.clone());
    let mut krate = source(Expr::bool_lit(false, SpanId(0)), vec![], 0);
    krate.fns[0].requires = vec![
        clause(eq(first, number(3, small))),
        clause(eq(second, number(50_000, wide))),
    ];
    verdict(&krate, false);
}

#[test]
fn variant_and_result_type_tampering_are_malformed() {
    let value = ctor(1, Ty::Bool, 0, vec![]);
    for invalid in [
        Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::IsVariant {
                base: Box::new(value.clone()),
                variant: 9,
            },
        ),
        Expr::new(
            Ty::Unit,
            SpanId(0),
            ExprKind::IsVariant {
                base: Box::new(value),
                variant: 0,
            },
        ),
    ] {
        assert!(check_crate(&source(invalid, vec![], 0))
            .iter()
            .any(|error| error.class == WfClass::Malformed));
    }
    let invalid = eq(
        project(
            ctor(1, Ty::Bool, 1, vec![Expr::bool_lit(true, SpanId(0))]),
            Ty::Int(IntRange::U(8)),
        ),
        number(0, Ty::Int(IntRange::U(8))),
    );
    assert!(check_crate(&source(invalid, vec![], 0))
        .iter()
        .any(|error| error.class == WfClass::Malformed));
}

#[test]
fn recursive_sum_values_refuse_instead_of_gaining_a_layout() {
    let ty = sum(1, Ty::Bool);
    let mut krate = source(test(read(1, ty.clone()), 0), vec![ty.clone()], 0);
    krate.adts[0].variants[1].fields[0].ty = sum(1, Ty::Param(0));
    assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
    let generated = vcgen::generate(&krate);
    assert!(
        matches!(generated.get(fid()), Some(FnVcs::Refused(problem))
        if problem.tag == "enum-layout"),
        "{generated:?}"
    );
}

#[test]
fn isolated_bitvector_lane_does_not_inherit_sum_semantics() {
    let goal = test(ctor(1, Ty::Bool, 0, vec![]), 0);
    let mut krate = source(goal.clone(), vec![], 0);
    krate.architecture = bitvector::Architecture::Either32Or64;
    let Body::Stmts(block) = &mut krate.fns[0].body else {
        unreachable!()
    };
    block.stmts[0].kind = StmtKind::AssertBitVector {
        requires: vec![],
        ensures: vec![clause(goal)],
        architecture: bitvector::Architecture::Either32Or64,
        site: SiteId(0),
    };
    assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
    let generated = vcgen::generate(&krate);
    assert!(
        matches!(generated.get(fid()), Some(FnVcs::Refused(problem))
        if problem.tag.starts_with("bit-vector") && problem.detail.contains("enum")),
        "{generated:?}"
    );
}
