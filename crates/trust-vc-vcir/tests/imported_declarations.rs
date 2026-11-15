//! Signature-only imported classification, independent of source authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{
    self,
    term::{Sort, Term},
    FnVcs,
};
use trust_vc_vcir::*;

fn id(number: u64) -> FnId {
    FnId(DefHash::new(10, number))
}
fn set() -> Ty {
    Ty::Adt(AdtId(DefHash::new(10, 1)), vec![Ty::Param(0)])
}
fn local(ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode: Mode::Spec,
        mutable: false,
        kind,
        span: SpanId(0),
    }
}
fn imported(number: u64, result: Ty) -> FnDecl {
    FnDecl {
        id: id(number),
        name: "same_display_name".into(),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Imported,
        kind: FnKind::Function,
        type_params: vec!["A".into()],
        locals: vec![
            local(result, LocalKind::Return),
            local(set(), LocalKind::Param),
        ],
        params: vec![LocalId(1)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}
fn read(number: u32) -> Expr {
    Expr::read(Place::local(LocalId(number)), set(), SpanId(0))
}
fn call(function: u64, argument: Expr, result: Ty) -> Expr {
    Expr::new(
        result,
        SpanId(0),
        ExprKind::Call {
            callee: id(function),
            type_args: vec![Ty::Param(0)],
            args: vec![argument],
        },
    )
}
fn statement(kind: StmtKind) -> Stmt {
    Stmt {
        span: SpanId(0),
        kind,
    }
}
fn client(goal: Expr) -> FnDecl {
    let mut declaration = imported(99, Ty::Unit);
    declaration.role = FnRole::Item;
    declaration.mode = Mode::Proof;
    declaration.locals.push(local(set(), LocalKind::Param));
    declaration.params.push(LocalId(2));
    declaration.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Assert {
            expr: goal,
            site: SiteId(0),
            attrs: ClauseAttrs::default(),
        }),
        statement(StmtKind::Return {
            value: None,
            site: SiteId(1),
        }),
    ]));
    declaration
}
fn source(goal: Expr) -> VcCrate {
    let mut krate = VcCrate::new("imported signature classification");
    krate.adts.push(AdtDecl {
        id: AdtId(DefHash::new(10, 1)),
        name: "Abstract".into(),
        type_params: vec!["A".into()],
        kind: AdtKind::Opaque,
        variants: vec![],
        span: SpanId(0),
    });
    krate.fns = vec![imported(1, Ty::nat()), client(goal)];
    krate
}
fn natural_goal(argument: Expr) -> Expr {
    Expr::binary(
        BinOp::Ge,
        call(1, argument, Ty::nat()),
        Expr::int_lit(0, Ty::nat(), SpanId(0)),
        Ty::Bool,
        SpanId(0),
    )
}
fn query(krate: &VcCrate) -> vcgen::Query {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let vcs = vcgen::generate(krate);
    assert!(matches!(vcs.get(id(1)), Some(FnVcs::Declared)));
    let Some(FnVcs::Checks(checks)) = vcs.get(id(99)) else {
        panic!("{vcs:?}");
    };
    assert_eq!(checks.len(), 1);
    assert!(!checks[0].order_unknown);
    checks[0].query.clone()
}
fn answer(query: &vcgen::Query, positive: bool) {
    #[cfg(feature = "solve")]
    {
        let result = solve::check(query, "imported signature", &solve::Limits::default());
        assert!(
            if positive {
                matches!(result, solve::Verdict::Proved { .. })
            } else {
                matches!(result, solve::Verdict::Refuted { .. })
            },
            "{result:?}"
        );
    }
    #[cfg(not(feature = "solve"))]
    let _ = (query, positive);
}

#[test]
fn imported_signatures_are_declared_with_guarded_typing_and_no_body() {
    let mut krate = source(natural_goal(read(1)));
    krate
        .def_order
        .insert(id(99), [(id(1), DefOrder::Later)].into_iter().collect());
    let generated = query(&krate);
    assert!(generated.definitions.is_empty());
    assert!(generated.nominal_types.is_empty());
    assert!(generated.functions.iter().any(|function| function.params
        == [Sort::Decoration, Sort::TypeId, Sort::Poly]
        && function.ret == Sort::Int));
    assert!(generated
        .hypotheses
        .iter()
        .any(|hypothesis| matches!(&hypothesis.term,
        Term::Implies(_, conclusion) if **conclusion == generated.goal)));
    assert!(generated
        .hypotheses
        .iter()
        .all(|hypothesis| hypothesis.term != generated.goal));
    answer(&generated, true);
    let wrong = Expr::binary(
        BinOp::Eq,
        call(1, read(1), Ty::nat()),
        call(1, read(2), Ty::nat()),
        Ty::Bool,
        SpanId(0),
    );
    answer(&query(&source(wrong)), false);
}

#[test]
fn monomorphic_imported_typing_keeps_its_native_argument_guard() {
    for minimum in [0, 1] {
        let x = Expr::read(Place::local(LocalId(1)), Ty::nat(), SpanId(0));
        let application = Expr::new(
            Ty::nat(),
            SpanId(0),
            ExprKind::Call {
                callee: id(1),
                type_args: vec![],
                args: vec![x],
            },
        );
        let goal = Expr::binary(
            BinOp::Ge,
            application,
            Expr::int_lit(minimum, Ty::nat(), SpanId(0)),
            Ty::Bool,
            SpanId(0),
        );
        let mut krate = source(goal);
        for declaration in &mut krate.fns {
            declaration.type_params.clear();
            declaration.params.truncate(1);
            declaration.locals.truncate(2);
            declaration.locals[1].ty = Ty::nat();
        }
        let generated = query(&krate);
        assert!(generated.definitions.is_empty());
        if minimum == 0 {
            assert!(generated
                .hypotheses
                .iter()
                .any(|hypothesis| matches!(&hypothesis.term,
            Term::Implies(_, conclusion) if **conclusion == generated.goal)));
        }
        assert!(generated
            .hypotheses
            .iter()
            .all(|hypothesis| hypothesis.term != generated.goal));
        answer(&generated, minimum == 0);
    }
}

#[test]
fn an_imported_role_cannot_authorize_a_body_contract_or_other_mode() {
    let base = source(natural_goal(read(1)));
    let variants: [fn(&mut FnDecl); 16] = [
        |declaration| declaration.body = Body::Spec(Expr::int_lit(0, Ty::nat(), SpanId(0))),
        |declaration| declaration.mode = Mode::Proof,
        |declaration| declaration.kind = FnKind::ConstFunction,
        |declaration| {
            declaration.ensures.push(Clause {
                expr: Expr::bool_lit(false, SpanId(0)),
                span: SpanId(0),
                attrs: ClauseAttrs::default(),
            })
        },
        |declaration| {
            declaration.requires.push(Clause {
                expr: Expr::bool_lit(true, SpanId(0)),
                span: SpanId(0),
                attrs: ClauseAttrs::default(),
            })
        },
        |declaration| {
            declaration.recommends.push(Clause {
                expr: Expr::bool_lit(true, SpanId(0)),
                span: SpanId(0),
                attrs: ClauseAttrs::default(),
            })
        },
        |declaration| {
            declaration
                .decreases
                .push(Expr::int_lit(0, Ty::nat(), SpanId(0)))
        },
        |declaration| declaration.decreases_when = Some(Expr::bool_lit(true, SpanId(0))),
        |declaration| declaration.decreases_by = Some(id(99)),
        |declaration| declaration.attrs.external_body = true,
        |declaration| declaration.attrs.exec_allows_no_decreases = true,
        |declaration| declaration.attrs.is_trait_method_impl = true,
        |declaration| declaration.attrs.is_decreases_by = true,
        |declaration| {
            declaration.attrs.instance = Some(GenericInstance {
                declaration: id(1),
                type_args: vec![Ty::Bool],
            })
        },
        |declaration| declaration.locals[1].mode = Mode::Proof,
        |declaration| declaration.locals[1].mutable = true,
    ];
    for mutate in variants {
        let mut krate = base.clone();
        mutate(&mut krate.fns[0]);
        assert!(check_crate(&krate)
            .iter()
            .any(|error| error.class == WfClass::Malformed && error.function == Some(id(1))));
        let vcs = vcgen::generate(&krate);
        assert!(matches!(vcs.get(id(1)), Some(FnVcs::Refused(_))), "{vcs:?}");
        assert!(
            matches!(vcs.get(id(99)), Some(FnVcs::Refused(_))),
            "{vcs:?}"
        );
    }
}

#[test]
fn imported_signatures_have_no_recursion_or_instance_origin_authority() {
    let mut krate = source(natural_goal(read(1)));
    krate.rec_groups.push(RecGroup {
        members: vec![(id(1), 1)],
    });
    assert!(check_crate(&krate)
        .iter()
        .any(|error| error.function == Some(id(1)) && error.class == WfClass::Malformed));
    assert!(matches!(
        vcgen::generate(&krate).get(id(99)),
        Some(FnVcs::Refused(_))
    ));
    let mut krate = source(natural_goal(read(1)));
    let mut instance = krate.fns[0].clone();
    instance.id = id(2);
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    for local in &mut instance.locals {
        local.ty = local.ty.subst(&[Ty::Bool]);
    }
    instance.attrs.instance = Some(GenericInstance {
        declaration: id(1),
        type_args: vec![Ty::Bool],
    });
    krate.fns.push(instance);
    assert!(check_crate(&krate)
        .iter()
        .any(|error| error.function == Some(id(2)) && error.class == WfClass::Malformed));
}

#[test]
fn imported_body_visibility_cannot_be_revealed_or_hidden() {
    for reveal in [false, true] {
        for live in [false, true] {
            let mut krate = source(natural_goal(read(1)));
            let Body::Stmts(block) = &mut krate.fns[1].body else {
                unreachable!()
            };
            let visibility = statement(if reveal {
                StmtKind::Reveal {
                    callee: id(1),
                    fuel: Some(1),
                }
            } else {
                StmtKind::Hide { callee: id(1) }
            });
            block.stmts.insert(
                0,
                statement(StmtKind::If {
                    cond: Expr::bool_lit(live, SpanId(0)),
                    then_block: Block::new(vec![visibility]),
                    else_block: Block::new(vec![]),
                }),
            );
            let errors = check_crate(&krate);
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].function, Some(id(99)));
            assert_eq!(errors[0].class, WfClass::Malformed);
            assert_eq!(errors[0].message, "in `same_display_name`: reveal or hide of an imported signature without body authority");
            assert!(
                matches!(vcgen::generate(&krate).get(id(99)), Some(FnVcs::Refused(problem)) if problem.tag == "imported-reveal")
            );
        }
    }
}

#[test]
fn imported_declaration_identity_does_not_follow_a_display_name() {
    for same in [false, true] {
        let goal = Expr::binary(
            BinOp::Eq,
            call(1, read(1), Ty::nat()),
            call(if same { 1 } else { 2 }, read(1), Ty::nat()),
            Ty::Bool,
            SpanId(0),
        );
        let mut krate = source(goal);
        krate.fns.insert(1, imported(2, Ty::nat()));
        answer(&query(&krate), same);
    }
}

#[test]
fn opaque_imported_results_supply_only_guarded_membership() {
    for same in [false, true] {
        let left = call(2, read(1), set());
        let goal = if same {
            natural_goal(left)
        } else {
            Expr::binary(
                BinOp::Eq,
                call(1, left, Ty::nat()),
                call(1, call(2, read(2), set()), Ty::nat()),
                Ty::Bool,
                SpanId(0),
            )
        };
        let mut krate = source(goal);
        krate.fns.insert(1, imported(2, set()));
        let query = query(&krate);
        assert!(query.definitions.is_empty());
        answer(&query, same);
    }
}
