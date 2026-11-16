//! Separate semantic definitions cannot mutate bodyless imported declarations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{self, term::Term, FnVcs};
use trust_vc_vcir::*;

fn id(value: u64) -> FnId {
    FnId(DefHash::new(77, value))
}
fn span() -> SpanId {
    SpanId(0)
}
fn local(ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "source name".into(),
        ty,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: false,
        kind,
        span: span(),
    }
}
fn declaration(owner: u64, parameters: usize) -> FnDecl {
    // Source parameters start at 1, while the client puts its return last.
    let mut locals = vec![local(Ty::int(), LocalKind::Return)];
    locals.extend((0..parameters).map(|_| local(Ty::int(), LocalKind::Param)));
    FnDecl {
        id: id(owner),
        name: "same display name".into(),
        span: span(),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals,
        params: (1..=parameters as u32).map(LocalId).collect(),
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
fn read(index: u32) -> Expr {
    Expr::read(Place::local(LocalId(index)), Ty::int(), span())
}
fn integer(value: i128) -> Expr {
    Expr::int_lit(value, Ty::int(), span())
}
fn binary(op: BinOp, left: Expr, right: Expr, ty: Ty) -> Expr {
    Expr::binary(op, left, right, ty, span())
}
fn call(owner: u64, arguments: Vec<Expr>) -> Expr {
    Expr::new(
        Ty::int(),
        span(),
        ExprKind::Call {
            callee: id(owner),
            type_args: vec![],
            args: arguments,
        },
    )
}
fn semantic_source() -> VcCrate {
    let mut add = declaration(1, 2);
    add.locals.push(local(Ty::int(), LocalKind::Bound));
    add.body = Body::Spec(Expr::new(
        Ty::int(),
        span(),
        ExprKind::Let {
            local: LocalId(3),
            value: Box::new(binary(BinOp::Add, read(1), read(2), Ty::int())),
            body: Box::new(read(3)),
        },
    ));
    // A false recommendation must never prove a wrong client assertion.
    add.recommends.push(Clause {
        expr: Expr::bool_lit(false, span()),
        span: span(),
        attrs: ClauseAttrs::default(),
    });
    let mut max = declaration(2, 2);
    max.body = Body::Spec(Expr::new(
        Ty::int(),
        span(),
        ExprKind::If {
            cond: Box::new(binary(BinOp::Ge, read(1), read(2), Ty::Bool)),
            then_expr: Box::new(read(1)),
            else_expr: Box::new(read(2)),
        },
    ));
    let mut max3 = declaration(3, 3);
    max3.body = Body::Spec(call(2, vec![call(2, vec![read(1), read(2)]), read(3)]));
    let mut source = VcCrate::new("complete source semantic view");
    source.fns = vec![add, max, max3];
    source
}
fn client(goal: Expr) -> VcCrate {
    let mut client = VcCrate::new("current client");
    client.fns = semantic_source()
        .fns
        .into_iter()
        .map(|source| {
            let count = source.params.len();
            let mut declaration = declaration(
                if source.id == id(1) {
                    1
                } else if source.id == id(2) {
                    2
                } else {
                    3
                },
                count,
            );
            declaration.role = FnRole::Imported;
            declaration.locals = (0..count)
                .map(|_| local(Ty::int(), LocalKind::Param))
                .collect();
            declaration.locals.push(local(Ty::int(), LocalKind::Return));
            declaration.params = (0..count as u32).map(LocalId).collect();
            declaration.ret = LocalId(count as u32);
            declaration
        })
        .collect();
    let mut proof = declaration(99, 0);
    proof.mode = Mode::Proof;
    proof.locals[0].ty = Ty::Unit;
    proof.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            span(),
            StmtKind::Assert {
                expr: goal,
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            },
        ),
        Stmt::new(
            span(),
            StmtKind::Return {
                value: None,
                site: SiteId(1),
            },
        ),
    ]));
    client.fns.push(proof);
    client
}
fn query(client: &VcCrate, definitions: &CheckedSpecDefinitions) -> vcgen::Query {
    assert!(check_crate(client).is_empty(), "{:?}", check_crate(client));
    let generated = vcgen::generate_with_spec_definitions(client, definitions);
    for owner in [1, 2, 3] {
        assert_eq!(generated.get(id(owner)), Some(&FnVcs::Declared));
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id(99)) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 1);
    checks[0].query.clone()
}

#[test]
fn checked_add_max_and_max3_define_calls_without_installing_bodies_or_assuming_recommends() {
    let source = semantic_source();
    let definitions = CheckedSpecDefinitions::from_crate(&source, &[id(1), id(2), id(3)]).unwrap();
    assert_eq!(definitions.len(), 3);
    assert_eq!(
        definitions
            .definitions()
            .find(|d| d.id == id(1))
            .unwrap()
            .recommends
            .len(),
        1
    );
    for (owner, arguments, result) in [
        (1, vec![2, 3], 5),
        (2, vec![2, 3], 3),
        (3, vec![2, 7, 3], 7),
    ] {
        for correct in [false, true] {
            let goal = binary(
                BinOp::Eq,
                call(owner, arguments.iter().copied().map(integer).collect()),
                integer(result + if correct { 0 } else { 1 }),
                Ty::Bool,
            );
            let client = client(goal);
            let before = client.clone();
            let generated = query(&client, &definitions);
            assert_eq!(generated.goal, Term::Bool(correct), "{generated:?}");
            assert_eq!(client, before);
        }
    }
}

#[test]
fn signature_only_calls_keep_their_uninterpreted_meaning() {
    let goal = binary(
        BinOp::Eq,
        call(1, vec![integer(2), integer(3)]),
        integer(5),
        Ty::Bool,
    );
    let client = client(goal);
    let generated = query(&client, &CheckedSpecDefinitions::default());
    assert_ne!(generated.goal, Term::Bool(true));
    assert_ne!(generated.goal, Term::Bool(false));
    assert_eq!(
        vcgen::generate(&client),
        vcgen::generate_with_spec_definitions(&client, &CheckedSpecDefinitions::default())
    );
}

#[test]
fn semantic_source_is_strictly_checked_before_bodies_are_retained() {
    let mut source = semantic_source();
    let Body::Spec(expression) = &mut source.fns[0].body else {
        unreachable!()
    };
    expression.ty = Ty::Bool;
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1), id(2), id(3)]).is_err());
    let mut source = semantic_source();
    source.fns[0].role = FnRole::Imported;
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1), id(2), id(3)]).is_err());
    let source = semantic_source();
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1), id(1)]).is_err());
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(404)]).is_err());
}

#[test]
fn recursive_or_incomplete_definition_closures_are_refused() {
    let mut source = semantic_source();
    source.fns[0].body = Body::Spec(call(1, vec![read(1), read(2)]));
    assert!(check_crate(&source).is_empty());
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1)]).is_err());
    let mut source = semantic_source();
    source.fns[0].body = Body::Spec(call(2, vec![read(1), read(2)]));
    source.fns[1].body = Body::Spec(call(1, vec![read(1), read(2)]));
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1)]).is_err());
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(1), id(2)]).is_err());
    assert!(CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(3)]).is_err());
}

#[test]
fn current_native_signature_join_is_rechecked_at_every_consumption() {
    let definitions =
        CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(1), id(2), id(3)]).unwrap();
    let base = client(Expr::bool_lit(true, span()));
    let mutations: [fn(&mut VcCrate); 5] = [
        |client| {
            client.fns[0].locals[0].ty = Ty::nat();
        },
        |client| {
            client.fns[0].id = id(404);
        },
        |client| {
            client.fns[0].body = Body::Spec(integer(0));
        },
        |client| {
            client.fns[1].role = FnRole::Item;
        },
        |client| {
            client.architecture = bitvector::Architecture::Exactly(32);
        },
    ];
    for mutate in mutations {
        let mut client = base.clone();
        mutate(&mut client);
        assert!(definitions.validate_for_crate(&client).is_err());
        assert!(vcgen::generate_with_spec_definitions(&client, &definitions).fns.iter().all(|(_, value)| matches!(value, FnVcs::Refused(problem) if problem.tag == "imported-definition")));
        assert!(vcgen::Recommendations::new_with_spec_definitions(&client, &definitions).is_err());
    }
}

#[test]
fn an_uninterpreted_source_dependency_still_requires_its_exact_current_signature() {
    let mut source = semantic_source();
    source.fns[1].body = Body::None;
    let definitions = CheckedSpecDefinitions::from_crate(&source, &[id(3)]).unwrap();
    let mut client = client(Expr::bool_lit(true, span()));
    assert!(definitions.validate_for_crate(&client).is_ok());
    client.fns[1].locals[0].ty = Ty::nat();
    assert!(definitions.validate_for_crate(&client).is_err());
}

#[test]
fn signature_matching_preserves_parameter_order_across_different_local_tables() {
    let mut source = VcCrate::new("mixed scalar signature");
    let mut function = declaration(1, 2);
    function.locals[1].ty = Ty::Bool;
    function.body = Body::Spec(read(2));
    source.fns.push(function);
    let definitions = CheckedSpecDefinitions::from_crate(&source, &[id(1)]).unwrap();
    let mut client = client(Expr::bool_lit(true, span()));
    client.fns[0].locals[0].ty = Ty::Bool;
    assert!(definitions.validate_for_crate(&client).is_ok());
    client.fns[0].params.swap(0, 1);
    assert!(check_crate(&client).is_empty());
    assert!(definitions.validate_for_crate(&client).is_err());
}

fn recommendation_query(client: &VcCrate, definitions: &CheckedSpecDefinitions) -> vcgen::Query {
    let checks = vcgen::Recommendations::new_with_spec_definitions(client, definitions)
        .expect("checked diagnostic definition view")
        .function(id(99))
        .expect("caller recommendation queries");
    assert_eq!(checks.len(), 1, "{checks:?}");
    assert!(matches!(&checks[0].kind,
        vcgen::CheckKind::Recommendation { callee, clause: 0, .. } if *callee == id(1)));
    checks[0].query.clone()
}

fn parameter_recommendation(first: i128, second: i128, expected: bool) {
    let mut source = semantic_source();
    source.fns[0].recommends[0].expr = binary(BinOp::Ge, read(1), integer(0), Ty::Bool);
    let definitions = CheckedSpecDefinitions::from_crate(&source, &[id(1), id(2), id(3)])
        .expect("checked source recommends");
    let client = client(binary(
        BinOp::Eq,
        call(1, vec![integer(first), integer(second)]),
        integer(first + second),
        Ty::Bool,
    ));
    let before = client.clone();
    assert!(client.fns[..3]
        .iter()
        .all(|declaration| declaration.recommends.is_empty()));
    let diagnostic = recommendation_query(&client, &definitions);
    // The source's first parameter is LocalId(1); the client's first parameter
    // is LocalId(0). Opposite-signed arguments detect an accidental second-arg
    // lookup through the client's local table.
    assert_eq!(diagnostic.goal, Term::Bool(expected), "{diagnostic:?}");
    assert_eq!(query(&client, &definitions).goal, Term::Bool(true));
    assert_eq!(client, before);
    assert!(vcgen::Recommendations::new(&client)
        .unwrap()
        .function(id(99))
        .unwrap()
        .is_empty());
}

#[test]
fn checked_import_recommendation_checks_the_positive_source_parameter() {
    parameter_recommendation(2, -7, true);
}

#[test]
fn checked_import_recommendation_checks_the_negative_source_parameter() {
    parameter_recommendation(-2, 7, false);
}

#[test]
fn false_checked_recommendations_are_diagnostics_and_cannot_prove_a_wrong_goal() {
    let definitions =
        CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(1), id(2), id(3)]).unwrap();
    let client = client(binary(
        BinOp::Eq,
        call(1, vec![integer(2), integer(3)]),
        integer(6),
        Ty::Bool,
    ));
    let before = client.clone();
    let normal = query(&client, &definitions);
    assert_eq!(normal.goal, Term::Bool(false));
    assert!(normal
        .hypotheses
        .iter()
        .all(|hypothesis| hypothesis.term != Term::Bool(false)));
    let diagnostic = recommendation_query(&client, &definitions);
    assert_eq!(diagnostic.goal, Term::Bool(false));
    assert!(diagnostic
        .hypotheses
        .iter()
        .all(|hypothesis| hypothesis.term != Term::Bool(false)));
    assert_eq!(query(&client, &definitions), normal);
    assert_eq!(client, before);
}

#[test]
fn bodyless_recommendations_rebind_parameters_without_defining_the_function() {
    let mut source = semantic_source();
    source.fns[0].body = Body::None;
    source.fns[0].attrs.external_body = true;
    source.fns[0].recommends[0].expr = binary(BinOp::Ge, read(1), integer(0), Ty::Bool);
    let checked =
        CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(&source, &[], &[id(1)])
            .unwrap();
    assert!(checked.is_empty());
    assert_eq!(checked.len(), 0);
    assert_eq!(checked.definitions().count(), 0);
    for (first, second, expected) in [(2, -7, true), (-2, 7, false)] {
        let client = client(binary(
            BinOp::Eq,
            call(1, vec![integer(first), integer(second)]),
            integer(5),
            Ty::Bool,
        ));
        let before = client.clone();
        assert_eq!(
            recommendation_query(&client, &checked).goal,
            Term::Bool(expected)
        );
        let normal = query(&client, &checked);
        assert_eq!(normal, query(&client, &CheckedSpecDefinitions::default()));
        assert!(!matches!(normal.goal, Term::Bool(_)));
        assert!(normal
            .hypotheses
            .iter()
            .all(|h| h.term != Term::Bool(false)));
        assert_eq!(client, before);
    }
}

fn generic_bodyless_source() -> VcCrate {
    let nominal = AdtId(DefHash::new(77, 7));
    let mut declaration = declaration(1, 2);
    declaration.type_params = vec!["A".into()];
    declaration.locals[0].ty = Ty::Param(0);
    declaration.locals[1].ty = Ty::Adt(nominal, vec![Ty::Param(0)]);
    declaration.recommends.push(Clause {
        expr: binary(BinOp::Ge, read(2), integer(0), Ty::Bool),
        span: span(),
        attrs: ClauseAttrs::default(),
    });
    let mut source = VcCrate::new("abstract generic recommendation source");
    source.adts.push(AdtDecl {
        id: nominal,
        name: "abstract carrier".into(),
        span: span(),
        type_params: vec!["A".into()],
        kind: AdtKind::Opaque,
        variants: vec![],
    });
    source.fns.push(declaration);
    source
}

fn generic_bodyless_client(index: i128) -> VcCrate {
    let source = generic_bodyless_source();
    let mut client = VcCrate::new("current abstract generic client");
    client.adts = source.adts.clone();
    let source_function = &source.fns[0];
    let mut imported = source_function.clone();
    imported.role = FnRole::Imported;
    imported.recommends.clear();
    // Source uses result0/self1/index2; client uses self0/index1/result2.
    imported.locals = vec![
        source_function.locals[1].clone(),
        source_function.locals[2].clone(),
        source_function.locals[0].clone(),
    ];
    imported.params = vec![LocalId(0), LocalId(1)];
    imported.ret = LocalId(2);
    client.fns.push(imported);
    let carrier = Ty::Adt(client.adts[0].id, vec![Ty::int()]);
    let value = Expr::new(
        Ty::int(),
        span(),
        ExprKind::Call {
            callee: id(1),
            type_args: vec![Ty::int()],
            args: vec![
                Expr::read(Place::local(LocalId(1)), carrier.clone(), span()),
                integer(index),
            ],
        },
    );
    let mut proof = declaration(99, 0);
    proof.mode = Mode::Proof;
    proof.locals[0].ty = Ty::Unit;
    proof.locals.push(local(carrier, LocalKind::Param));
    proof.params.push(LocalId(1));
    proof.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            span(),
            StmtKind::Assert {
                expr: binary(BinOp::Eq, value, integer(0), Ty::Bool),
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            },
        ),
        Stmt::new(
            span(),
            StmtKind::Return {
                value: None,
                site: SiteId(1),
            },
        ),
    ]));
    client.fns.push(proof);
    client
}

#[test]
fn generic_opaque_recommendations_keep_uninterpreted_results_arbitrary() {
    let source = generic_bodyless_source();
    let checked =
        CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(&source, &[], &[id(1)])
            .unwrap();
    for (index, expected) in [(2, true), (-2, false)] {
        let client = generic_bodyless_client(index);
        let before = client.clone();
        assert_eq!(
            recommendation_query(&client, &checked).goal,
            Term::Bool(expected)
        );
        let with = vcgen::generate_with_spec_definitions(&client, &checked);
        assert_eq!(with, vcgen::generate(&client));
        let Some(FnVcs::Checks(checks)) = with.get(id(99)) else {
            panic!("{with:?}")
        };
        assert!(!matches!(checks[0].query.goal, Term::Bool(_)));
        assert_eq!(client, before);
    }
}

#[test]
fn bodyless_recommendation_owners_and_dependencies_require_current_signatures() {
    let source = generic_bodyless_source();
    let checked =
        CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(&source, &[], &[id(1)])
            .unwrap();
    let base = generic_bodyless_client(2);
    for mutate in [
        |client: &mut VcCrate| {
            client.fns[0].params.swap(0, 1);
        },
        |client: &mut VcCrate| {
            client.fns[0].locals[1].ty = Ty::nat();
        },
        |client: &mut VcCrate| {
            client.fns[0].id = id(404);
        },
        |client: &mut VcCrate| {
            client.adts[0].kind = AdtKind::Struct;
        },
        |client: &mut VcCrate| {
            client.adts[0].type_params.push("B".into());
        },
        |client: &mut VcCrate| {
            client.architecture = bitvector::Architecture::Exactly(32);
        },
    ] {
        let mut client = base.clone();
        mutate(&mut client);
        assert!(checked.validate_for_crate(&client).is_err());
        assert!(vcgen::Recommendations::new_with_spec_definitions(&client, &checked).is_err());
    }
    assert!(
        CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(
            &source,
            &[],
            &[id(1), id(1)],
        )
        .is_err()
    );
    assert!(
        CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(&source, &[], &[id(404)],)
            .is_err()
    );
    for change in [
        |source: &mut VcCrate| {
            source.fns[0].body = Body::Spec(read(2));
        },
        |source: &mut VcCrate| {
            source.fns[0].mode = Mode::Proof;
        },
        |source: &mut VcCrate| {
            source.fns[0].recommends.clear();
        },
    ] {
        let mut mutated = source.clone();
        change(&mut mutated);
        assert!(
            CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(
                &mutated,
                &[],
                &[id(1)],
            )
            .is_err()
        );
    }
}

#[test]
fn recommendation_dependency_cycles_do_not_recursively_assume_their_predicates() {
    let mut source = semantic_source();
    for owner in [0, 1] {
        source.fns[owner].body = Body::None;
        source.fns[owner].recommends = vec![Clause {
            expr: binary(
                BinOp::Ge,
                call(if owner == 0 { 2 } else { 1 }, vec![read(1), read(2)]),
                integer(0),
                Ty::Bool,
            ),
            span: span(),
            attrs: ClauseAttrs::default(),
        }];
    }
    let checked = CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(
        &source,
        &[],
        &[id(1), id(2)],
    )
    .unwrap();
    let client = client(binary(
        BinOp::Eq,
        call(1, vec![integer(2), integer(3)]),
        integer(5),
        Ty::Bool,
    ));
    let diagnostic = recommendation_query(&client, &checked);
    assert!(!matches!(diagnostic.goal, Term::Bool(_)));
    assert!(diagnostic
        .hypotheses
        .iter()
        .all(|h| h.term != Term::Bool(false)));
    assert_eq!(
        query(&client, &checked),
        query(&client, &CheckedSpecDefinitions::default())
    );
}

fn forwarding_source() -> VcCrate {
    let mut source = generic_bodyless_source();
    let mut forwarder = source.fns[0].clone();
    forwarder.id = id(2);
    forwarder.attrs.inline = true;
    forwarder.body = Body::Spec(Expr::new(
        Ty::Param(0),
        span(),
        ExprKind::Call {
            callee: id(1),
            type_args: vec![Ty::Param(0)],
            args: vec![
                Expr::read(
                    Place::local(LocalId(1)),
                    forwarder.locals[1].ty.clone(),
                    span(),
                ),
                read(2),
            ],
        },
    ));
    source.fns.push(forwarder);
    source
}

fn forwarding_call(client: &VcCrate, owner: u64, index: i128) -> Expr {
    Expr::new(
        Ty::int(),
        span(),
        ExprKind::Call {
            callee: id(owner),
            type_args: vec![Ty::int()],
            args: vec![
                Expr::read(
                    Place::local(LocalId(1)),
                    Ty::Adt(client.adts[0].id, vec![Ty::int()]),
                    span(),
                ),
                integer(index),
            ],
        },
    )
}

fn forwarding_client(index: i128, correct: Option<bool>) -> VcCrate {
    let mut client = generic_bodyless_client(index);
    let mut signature = client.fns[0].clone();
    signature.id = id(2);
    client.fns.insert(1, signature);
    let value = forwarding_call(&client, 2, index);
    let goal = match correct {
        Some(correct) => binary(
            if correct { BinOp::Eq } else { BinOp::Ne },
            value,
            forwarding_call(&client, 1, index),
            Ty::Bool,
        ),
        None => binary(BinOp::Eq, value, integer(0), Ty::Bool),
    };
    let Body::Stmts(block) = &mut client.fns.last_mut().unwrap().body else {
        unreachable!()
    };
    let StmtKind::Assert { expr, .. } = &mut block.stmts[0].kind else {
        unreachable!()
    };
    *expr = goal;
    client
}

fn forwarding_query(client: &VcCrate, checked: &CheckedSpecDefinitions) -> vcgen::Query {
    assert!(check_crate(client).is_empty(), "{:?}", check_crate(client));
    let generated = vcgen::generate_with_spec_definitions(client, checked);
    for owner in [1, 2] {
        assert_eq!(generated.get(id(owner)), Some(&FnVcs::Declared));
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id(99)) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 1, "{checks:?}");
    checks[0].query.clone()
}

#[test]
fn exact_generic_forwarder_uses_its_body_without_defining_the_uninterpreted_target() {
    let source = forwarding_source();
    let checked =
        CheckedSpecDefinitions::from_crate_with_forwarders(&source, &[], &[id(1)], &[id(2)])
            .unwrap();
    assert_eq!(checked.len(), 1);
    assert_eq!(
        checked.definitions().map(|d| d.id).collect::<Vec<_>>(),
        vec![id(2)]
    );
    assert!(CheckedSpecDefinitions::from_crate(&source, &[id(2)]).is_err());
    for correct in [false, true] {
        let client = forwarding_client(2, Some(correct));
        let before = client.clone();
        assert!(client.fns[..2]
            .iter()
            .all(|d| matches!(d.body, Body::None) && d.recommends.is_empty() && !d.attrs.inline));
        assert_eq!(
            forwarding_query(&client, &checked).goal,
            Term::Bool(correct)
        );
        assert!(!matches!(
            forwarding_query(&client, &CheckedSpecDefinitions::default()).goal,
            Term::Bool(_)
        ));
        assert_eq!(client, before);
    }
    let mut client = forwarding_client(2, None);
    let value = forwarding_call(&client, 1, 2);
    let Body::Stmts(block) = &mut client.fns.last_mut().unwrap().body else {
        unreachable!()
    };
    let StmtKind::Assert { expr, .. } = &mut block.stmts[0].kind else {
        unreachable!()
    };
    *expr = binary(BinOp::Eq, value, integer(0), Ty::Bool);
    assert_eq!(
        forwarding_query(&client, &checked),
        forwarding_query(&client, &CheckedSpecDefinitions::default())
    );
}

#[test]
fn forwarded_recommendations_keep_each_source_local_table_and_never_assume_false() {
    let checked = CheckedSpecDefinitions::from_crate_with_forwarders(
        &forwarding_source(),
        &[],
        &[id(1)],
        &[id(2)],
    )
    .unwrap();
    for (index, expected) in [(2, true), (-2, false)] {
        let client = forwarding_client(index, Some(false));
        let before = client.clone();
        let checks = vcgen::Recommendations::new_with_spec_definitions(&client, &checked)
            .unwrap()
            .function(id(99))
            .unwrap();
        // The goal calls the wrapper and the target separately. The wrapper
        // also calls its target: retain all three actual call obligations.
        assert_eq!(checks.len(), 3, "{checks:?}");
        assert_eq!(
            checks
                .iter()
                .filter(|check| matches!(check.kind,
            vcgen::CheckKind::Recommendation { callee, .. } if callee == id(2)))
                .count(),
            1
        );
        assert_eq!(
            checks
                .iter()
                .filter(|check| matches!(check.kind,
            vcgen::CheckKind::Recommendation { callee, .. } if callee == id(1)))
                .count(),
            2
        );
        assert!(checks.iter().all(|c| c.query.goal == Term::Bool(expected)));
        assert_eq!(forwarding_query(&client, &checked).goal, Term::Bool(false));
        assert_eq!(client, before);
    }
}

#[test]
fn forwarder_selection_and_current_signature_changes_cannot_reuse_the_body() {
    let source = forwarding_source();
    let checked =
        CheckedSpecDefinitions::from_crate_with_forwarders(&source, &[], &[id(1)], &[id(2)])
            .unwrap();
    for mutate in [
        |client: &mut VcCrate| {
            client.fns[0].id = id(404);
        },
        |client: &mut VcCrate| {
            client.fns[1].id = id(405);
        },
        |client: &mut VcCrate| {
            client.fns[1].locals[1].ty = Ty::nat();
        },
        |client: &mut VcCrate| {
            client.fns[1].params.swap(0, 1);
        },
        |client: &mut VcCrate| {
            client.fns[1].body = Body::Spec(integer(0));
        },
        |client: &mut VcCrate| {
            client.adts[0].type_params.clear();
        },
    ] {
        let mut client = forwarding_client(2, Some(true));
        mutate(&mut client);
        assert!(checked.validate_for_crate(&client).is_err());
        assert!(vcgen::Recommendations::new_with_spec_definitions(&client, &checked).is_err());
    }
    assert!(CheckedSpecDefinitions::from_crate_with_forwarders(
        &source,
        &[],
        &[id(1)],
        &[id(2), id(2)]
    )
    .is_err());
    assert!(
        CheckedSpecDefinitions::from_crate_with_forwarders(&source, &[], &[], &[id(404)]).is_err()
    );
}

#[test]
fn finite_forwarders_reject_permuted_arguments_computation_and_defining_targets() {
    let mut source = semantic_source();
    // This control owns only the target and wrapper. An unrelated caller must
    // not preempt the separate well-formed prophetic declaration mutation.
    source.fns.truncate(2);
    source.fns[0].body = Body::None;
    source.fns[1].attrs.inline = true;
    source.fns[1].body = Body::Spec(call(1, vec![read(1), read(2)]));
    assert!(
        CheckedSpecDefinitions::from_crate_with_forwarders(&source, &[], &[], &[id(2)]).is_ok()
    );
    for mutate in [
        |source: &mut VcCrate| {
            let Body::Spec(Expr {
                kind: ExprKind::Call { args, .. },
                ..
            }) = &mut source.fns[1].body
            else {
                unreachable!()
            };
            args.swap(0, 1);
        },
        |source: &mut VcCrate| {
            source.fns[1].body = Body::Spec(call(
                1,
                vec![binary(BinOp::Add, read(1), integer(1), Ty::int()), read(2)],
            ));
        },
        |source: &mut VcCrate| {
            source.fns[0].body = Body::Spec(integer(0));
        },
        |source: &mut VcCrate| {
            source.fns[1].attrs.inline = false;
        },
        |source: &mut VcCrate| {
            source.fns[1].attrs.prophetic = true;
        },
    ] {
        let mut changed = source.clone();
        mutate(&mut changed);
        assert!(
            check_crate(&changed).is_empty(),
            "{:?}",
            check_crate(&changed)
        );
        assert!(
            CheckedSpecDefinitions::from_crate_with_forwarders(&changed, &[], &[], &[id(2)])
                .is_err()
        );
    }
}

fn open_forwarding_client(correct: bool) -> VcCrate {
    let mut client = forwarding_client(2, Some(correct));
    let nominal = client.adts[0].id;
    let invoke = |owner| {
        Expr::new(
            Ty::Param(0),
            span(),
            ExprKind::Call {
                callee: id(owner),
                type_args: vec![Ty::Param(0)],
                args: vec![
                    Expr::read(
                        Place::local(LocalId(1)),
                        Ty::Adt(nominal, vec![Ty::Param(0)]),
                        span(),
                    ),
                    integer(2),
                ],
            },
        )
    };
    let proof = client.fns.last_mut().unwrap();
    proof.type_params = vec!["CallerA".into()];
    proof.locals[1].ty = Ty::Adt(nominal, vec![Ty::Param(0)]);
    let Body::Stmts(block) = &mut proof.body else {
        unreachable!()
    };
    let StmtKind::Assert { expr, .. } = &mut block.stmts[0].kind else {
        unreachable!()
    };
    *expr = binary(
        if correct { BinOp::Eq } else { BinOp::Ne },
        invoke(2),
        invoke(1),
        Ty::Bool,
    );
    client
}

#[test]
fn open_caller_type_environment_preserves_the_exact_forwarded_value() {
    let checked = CheckedSpecDefinitions::from_crate_with_forwarders(
        &forwarding_source(),
        &[],
        &[id(1)],
        &[id(2)],
    )
    .unwrap();
    for correct in [false, true] {
        let client = open_forwarding_client(correct);
        let before = client.clone();
        assert_eq!(
            forwarding_query(&client, &checked).goal,
            Term::Bool(correct)
        );
        assert_eq!(client, before);
    }
}

#[cfg(feature = "solve")]
mod actual_solver {
    use super::*;
    use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};

    fn verdict(query: &vcgen::Query, correct: bool) {
        let result = check_detailed(
            query,
            "checked source definition control",
            &Limits::default(),
        );
        assert!(
            if correct {
                matches!(&result.verdict, Verdict::Proved { .. })
            } else {
                matches!(&result.verdict, Verdict::Refuted { .. })
            },
            "{result:?}"
        );
    }

    fn symbolic_client(goal: Expr) -> VcCrate {
        let mut client = client(goal);
        let proof = client.fns.last_mut().unwrap();
        for index in 1..=3 {
            proof.locals.push(local(Ty::int(), LocalKind::Param));
            proof.params.push(LocalId(index));
        }
        client
    }

    #[test]
    fn checked_add_max_and_max3_true_and_liar_twins_have_strict_solver_verdicts() {
        let definitions =
            CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(1), id(2), id(3)]).unwrap();
        for (owner, arguments, result) in [
            (1, vec![2, 3], 5),
            (2, vec![2, 3], 3),
            (3, vec![2, 7, 3], 7),
        ] {
            for correct in [false, true] {
                let client = client(binary(
                    BinOp::Eq,
                    call(owner, arguments.iter().copied().map(integer).collect()),
                    integer(result + if correct { 0 } else { 1 }),
                    Ty::Bool,
                ));
                let question = query(&client, &definitions);
                assert!(question
                    .hypotheses
                    .iter()
                    .all(|h| h.term != Term::Bool(false)));
                verdict(&question, correct);
            }
        }
    }

    #[test]
    fn symbolic_checked_equations_reach_the_solver_for_each_math_definition() {
        let definitions =
            CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(1), id(2), id(3)]).unwrap();
        for owner in [1, 2, 3] {
            for correct in [false, true] {
                let arguments = match owner {
                    1 => vec![read(1), integer(1)],
                    2 => vec![read(1), read(2)],
                    _ => vec![read(1), read(2), read(3)],
                };
                let op = match (owner, correct) {
                    (1, true) => BinOp::Gt,
                    (1, false) => BinOp::Le,
                    (_, true) => BinOp::Ge,
                    (_, false) => BinOp::Lt,
                };
                let client = symbolic_client(binary(op, call(owner, arguments), read(1), Ty::Bool));
                let question = query(&client, &definitions);
                assert!(!question.symbols.is_empty());
                assert!(!matches!(question.goal, Term::Bool(_)), "{question:?}");
                verdict(&question, correct);
            }
        }
    }

    #[test]
    fn a_signature_only_symbolic_call_has_a_counterexample() {
        let client = symbolic_client(binary(
            BinOp::Gt,
            call(1, vec![read(1), integer(1)]),
            read(1),
            Ty::Bool,
        ));
        verdict(&query(&client, &CheckedSpecDefinitions::default()), false);
    }

    #[test]
    fn false_recommendation_cannot_change_a_false_normal_solver_verdict() {
        let definitions =
            CheckedSpecDefinitions::from_crate(&semantic_source(), &[id(1), id(2), id(3)]).unwrap();
        let client = client(binary(
            BinOp::Eq,
            call(1, vec![integer(2), integer(3)]),
            integer(6),
            Ty::Bool,
        ));
        verdict(&query(&client, &definitions), false);
        verdict(&recommendation_query(&client, &definitions), false);
    }

    #[test]
    fn bodyless_recommendations_do_not_constrain_generic_results() {
        let checked = CheckedSpecDefinitions::from_crate_with_bodyless_recommendations(
            &generic_bodyless_source(),
            &[],
            &[id(1)],
        )
        .unwrap();
        for (index, expected) in [(2, true), (-2, false)] {
            let client = generic_bodyless_client(index);
            verdict(&recommendation_query(&client, &checked), expected);
            let generated = vcgen::generate_with_spec_definitions(&client, &checked);
            let Some(FnVcs::Checks(checks)) = generated.get(id(99)) else {
                panic!("{generated:?}")
            };
            verdict(&checks[0].query, false);
        }
    }

    #[test]
    fn checked_forwarding_equation_and_arbitrary_target_have_strict_solver_controls() {
        let checked = CheckedSpecDefinitions::from_crate_with_forwarders(
            &forwarding_source(),
            &[],
            &[id(1)],
            &[id(2)],
        )
        .unwrap();
        for (index, expected_recommendation) in [(2, true), (-2, false)] {
            for correct in [false, true] {
                let client = forwarding_client(index, Some(correct));
                verdict(&forwarding_query(&client, &checked), correct);
                for diagnostic in
                    vcgen::Recommendations::new_with_spec_definitions(&client, &checked)
                        .unwrap()
                        .function(id(99))
                        .unwrap()
                {
                    verdict(&diagnostic.query, expected_recommendation);
                }
            }
            verdict(
                &forwarding_query(&forwarding_client(index, None), &checked),
                false,
            );
        }
        for correct in [false, true] {
            verdict(
                &forwarding_query(&open_forwarding_client(correct), &checked),
                correct,
            );
        }
    }
}
