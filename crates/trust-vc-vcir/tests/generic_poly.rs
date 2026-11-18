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
        copy_premises: Vec::new(),
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

fn associated(id: u64, argument: Ty) -> Ty {
    Ty::Projection(ProjectionId(DefHash::new(88, id)), vec![argument])
}

fn associated_source() -> VcCrate {
    let mut source = source();
    for number in [1, 2] {
        source.projections.push(ProjectionDecl {
            id: ProjectionId(DefHash::new(88, number)),
            trait_id: DefHash::new(89, number),
            arity: 1,
            // Identical display names never establish member identity.
            name: "Trait::Item".into(), span: SpanId(0),
        });
    }
    source
}

#[test]
fn associated_type_call_arguments_preserve_member_and_self_identity() {
    for (member, parameter, same) in [(1, 0, true), (2, 0, false), (1, 1, false)] {
        let mut source = associated_source();
        source.fns.push(function(1, vec![], Ty::nat()));
        let left = call(1, vec![associated(1, Ty::Param(0))], vec![], Ty::nat());
        let right = call(1, vec![associated(member, Ty::Param(parameter))], vec![], Ty::nat());
        source.fns.push(client(binary(BinOp::Eq, left, right, Ty::Bool), vec![], 2));
        let result = verdict(&source);
        assert!(if same { matches!(result, Verdict::Proved { .. }) }
            else { matches!(result, Verdict::Refuted { .. }) }, "{result:?}");
    }
}

#[test]
fn wellformedness_refuses_malformed_associated_declarations_and_arguments() {
    for problem in 0..4 {
        let mut source = associated_source();
        source.fns.push(function(1, vec![], Ty::nat()));
        let mut argument = associated(1, Ty::Param(0));
        match problem {
            0 => source.projections.clear(),
            1 => source.projections.push(source.projections[0].clone()),
            2 => source.projections[0].arity = 2,
            3 => argument = associated(1, Ty::Param(3)),
            _ => unreachable!(),
        }
        let value = call(1, vec![argument], vec![], Ty::nat());
        source.fns.push(client(binary(BinOp::Ge, value, nat(0), Ty::Bool), vec![], 1));
        assert!(!check_crate(&source).is_empty());
    }
}

#[test]
fn projected_values_keep_membership_and_do_not_identify_distinct_inputs() {
    for false_claim in [false, true] {
        let mut source = associated_source();
        let ty = associated(1, Ty::Param(0));
        let mut identity = function(1, vec![ty.clone()], ty.clone());
        identity.body = Body::Spec(read(1, ty.clone()));
        source.fns.push(identity);
        let output = call(1, vec![Ty::Param(0)], vec![read(1, ty.clone())], ty.clone());
        let expected = read(if false_claim { 2 } else { 1 }, ty.clone());
        source.fns.push(client(binary(BinOp::Eq, output, expected, Ty::Bool), vec![ty.clone(), ty], 1));
        let actual = verdict(&source);
        assert!(if false_claim { matches!(actual, Verdict::Refuted { .. }) }
            else { matches!(actual, Verdict::Proved { .. }) }, "{actual:?}");
    }
}

fn closed_associated_source() -> VcCrate {
    let mut source = associated_source();
    source.projection_impls.push(ProjectionImpl {
        id: DefHash::new(90, 1), trait_id: source.projections[0].trait_id,
        arguments: vec![Ty::uint(8)],
        values: vec![ProjectionValue { declaration: source.projections[0].id,
            definition: DefHash::new(91, 1), ty: Ty::uint(16) }], span: SpanId(0),
    });
    source
}

#[test]
fn associated_fields_and_polymorphic_whole_products_share_closed_type_semantics() {
    let adt = AdtId(DefHash::new(92, 1));
    let product = |argument| Ty::Adt(adt, vec![argument]);
    for through_whole_value in [false, true] {
        for false_claim in [false, true] {
            let mut source = closed_associated_source();
            source.adts.push(AdtDecl { id: adt, name: "Carrier".into(), type_params: vec!["A".into()],
                span: SpanId(0), kind: AdtKind::Struct, variants: vec![VariantDecl { name: "Carrier".into(),
                    fields: vec![FieldDecl { name: "value".into(), ty: associated(1, Ty::Param(0)), mode: Mode::Exec }] }] });
            let value = Expr::new(product(Ty::uint(8)), SpanId(0), ExprKind::Ctor { adt, variant: 0,
                fields: vec![Expr::int_lit(7, Ty::uint(16), SpanId(0))] });
            let output = if through_whole_value {
                let mut identity = function(3, vec![Ty::Param(0)], Ty::Param(0));
                identity.body = Body::Spec(read(1, Ty::Param(0))); source.fns.push(identity);
                let returned = call(3, vec![product(Ty::uint(8))], vec![value], product(Ty::uint(8)));
                Expr::new(Ty::uint(16), SpanId(0), ExprKind::Field { base: Box::new(returned), variant: 0, field: 0 })
            } else {
                let mut get = function(3, vec![product(Ty::Param(0))], associated(1, Ty::Param(0)));
                get.body = Body::Spec(Expr::new(associated(1, Ty::Param(0)), SpanId(0), ExprKind::Field {
                    base: Box::new(read(1, product(Ty::Param(0)))), variant: 0, field: 0 }));
                source.fns.push(get);
                call(3, vec![Ty::uint(8)], vec![value], Ty::uint(16))
            };
            let expected = Expr::int_lit(if false_claim { 8 } else { 7 }, Ty::uint(16), SpanId(0));
            source.fns.push(client(binary(BinOp::Eq, output, expected, Ty::Bool), vec![], 0));
            let actual = verdict(&source);
            assert!(if false_claim { matches!(actual, Verdict::Refuted { .. }) }
                else { matches!(actual, Verdict::Proved { .. }) }, "{through_whole_value}/{false_claim}: {actual:?}");
        }
    }
}

#[test]
fn closed_native_instances_require_the_same_normalized_signature_and_body() {
    for false_claim in [false, true] {
        let mut source = closed_associated_source();
        let projected = associated(1, Ty::Param(0));
        let mut original = function(1, vec![projected.clone()], projected.clone());
        original.body = Body::Spec(read(1, projected));
        let mut instance = function(2, vec![Ty::uint(16)], Ty::uint(16));
        instance.type_params.clear();
        instance.role = FnRole::Instance;
        instance.attrs.instance = Some(GenericInstance { declaration: original.id, type_args: vec![Ty::uint(8)] });
        instance.body = Body::Spec(read(1, Ty::uint(16)));
        source.fns.extend([original, instance]);
        let input = Expr::int_lit(7, Ty::uint(16), SpanId(0));
        let output = call(2, vec![], vec![input], Ty::uint(16));
        let expected = Expr::int_lit(if false_claim { 8 } else { 7 }, Ty::uint(16), SpanId(0));
        source.fns.push(client(binary(BinOp::Eq, output, expected, Ty::Bool), vec![], 0));
        let actual = verdict(&source);
        assert!(if false_claim { matches!(actual, Verdict::Refuted { .. }) }
            else { matches!(actual, Verdict::Proved { .. }) }, "{actual:?}");
    }
}

#[test]
fn malformed_associated_implementations_never_relax_instance_typing() {
    for problem in 0..8 {
        let mut source = closed_associated_source();
        match problem {
            0 => source.projection_impls[0].trait_id = DefHash::new(999, 0),
            1 => source.projection_impls[0].values[0].declaration = source.projections[1].id,
            2 => source.projection_impls[0].arguments = vec![Ty::Param(0)],
            3 => source.projection_impls[0].values[0].ty = associated(1, Ty::uint(8)),
            4 => source.projection_impls[0].values[0].ty = associated(2, Ty::uint(8)),
            5 => { let mut other = source.projection_impls[0].clone(); other.id = DefHash::new(90, 2); source.projection_impls.push(other); }
            6 => { let repeated = source.projection_impls[0].values[0].clone(); source.projection_impls[0].values.push(repeated); }
            7 => source.projection_impls[0].arguments.push(Ty::Bool),
            _ => unreachable!(),
        }
        assert!(!check_crate(&source).is_empty(), "malformed definition {problem}");
    }
    let mut source = closed_associated_source();
    let projected = associated(1, Ty::Param(0));
    let mut original = function(1, vec![projected.clone()], projected.clone());
    original.body = Body::Spec(read(1, projected));
    let mut wrong = function(2, vec![Ty::Bool], Ty::Bool);
    wrong.type_params.clear(); wrong.role = FnRole::Instance;
    wrong.attrs.instance = Some(GenericInstance { declaration: original.id, type_args: vec![Ty::uint(8)] });
    wrong.body = Body::Spec(read(1, Ty::Bool)); source.fns.extend([original, wrong]);
    assert!(!check_crate(&source).is_empty());
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

#[test]
fn projected_field_cycles_and_wrong_closed_field_members_are_not_typing_facts() {
    let adt = AdtId(DefHash::new(92, 8));
    let mut source = closed_associated_source();
    source.adts.push(AdtDecl { id: adt, name: "Carrier".into(), type_params: vec!["A".into()],
        span: SpanId(0), kind: AdtKind::Struct, variants: vec![VariantDecl { name: "Carrier".into(),
            fields: vec![FieldDecl { name: "value".into(), ty: associated(1, Ty::Param(0)), mode: Mode::Exec }] }] });
    // The same actual closed domain would require its own full product
    // before its associated field can exist. Public IR gets no native
    // summary flag to erase that semantic cycle.
    source.projection_impls[0].values[0].ty = Ty::Adt(adt, vec![Ty::uint(8)]);
    assert!(!check_crate(&source).is_empty());
    source.projection_impls[0].values[0].ty = Ty::uint(16);
    let value = Expr::new(Ty::Adt(adt, vec![Ty::uint(8)]), SpanId(0), ExprKind::Ctor {
        adt, variant: 0, fields: vec![Expr::bool_lit(true, SpanId(0))] });
    source.fns.push(client(binary(BinOp::Eq, value.clone(), value, Ty::Bool), vec![], 0));
    assert!(!check_crate(&source).is_empty());
}
