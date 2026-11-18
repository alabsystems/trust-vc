//! Structured generic-instance origins, independent of diagnostic names.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::*;

#[path = "generic_origins/concrete_inline.rs"]
mod concrete_inline;

#[path = "generic_origins/copy_premises.rs"]
mod copy_premises;

fn id(value: u64) -> FnId {
    FnId(DefHash::new(4, value))
}

fn local(ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "same_name".into(),
        ty,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: false,
        kind,
        span: SpanId(0),
    }
}

fn original() -> FnDecl {
    FnDecl {
        id: id(1),
        name: "same_name".into(),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec!["A".into()],
        locals: vec![
            local(Ty::Param(0), LocalKind::Return),
            local(Ty::Param(0), LocalKind::Param),
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
        body: Body::None,
    }
}

fn source() -> VcCrate {
    let original = original();
    let mut instance = original.clone();
    instance.id = id(2);
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    for local in &mut instance.locals {
        local.ty = local.ty.subst(&[Ty::Bool]);
    }
    instance.attrs.instance = Some(GenericInstance {
        declaration: original.id,
        type_args: vec![Ty::Bool],
    });
    let mut krate = VcCrate::new("native instance origins");
    krate.fns = vec![original, instance];
    krate
}

fn has_malformed(krate: &VcCrate, function: FnId, message: &str) -> bool {
    let declaration = krate
        .fns
        .iter()
        .find(|declaration| declaration.id == function)
        .unwrap();
    let expected = format!("in `{}`: {message}", declaration.name);
    check_crate(krate).iter().any(|error| {
        error.class == WfClass::Malformed
            && error.function == Some(function)
            && error.message == expected
    })
}

#[test]
fn origin_checks_use_native_identity_and_complete_substitution() {
    let mut krate = source();
    assert!(check_crate(&krate).is_empty());
    krate.fns[1].name = "unrelated_display_name".into();
    assert!(check_crate(&krate).is_empty());
    krate.fns[1].attrs.instance.as_mut().unwrap().declaration = id(99);
    assert!(has_malformed(
        &krate,
        id(2),
        "an instance has no original declaration"
    ));
}

#[test]
fn incomplete_and_still_generic_origins_are_malformed() {
    for arguments in [vec![], vec![Ty::Bool, Ty::Bool], vec![Ty::Param(0)]] {
        let mut krate = source();
        krate.fns[1].attrs.instance.as_mut().unwrap().type_args = arguments;
        assert!(has_malformed(
            &krate,
            id(2),
            "an invalid generic instance origin or substitution"
        ));
    }
}

#[test]
fn forged_instance_signature_and_mode_do_not_authorize_a_bridge() {
    let mut wrong_type = source();
    wrong_type.fns[1].locals[0].ty = Ty::nat();
    let mut wrong_mode = source();
    wrong_mode.fns[1].locals[1].mode = Mode::Proof;
    let mut wrong_attribute = source();
    wrong_attribute.fns[1].attrs.opaque = true;
    for krate in [wrong_type, wrong_mode, wrong_attribute] {
        assert!(has_malformed(
            &krate,
            id(2),
            "an instance signature disagrees with its native origin"
        ));
    }
}

#[test]
fn instance_origins_cannot_chain_through_other_instances() {
    let mut krate = source();
    let mut chained = krate.fns[1].clone();
    chained.id = id(3);
    chained.attrs.instance.as_mut().unwrap().declaration = id(2);
    krate.fns.push(chained);
    assert!(has_malformed(
        &krate,
        id(3),
        "an invalid generic instance origin or substitution"
    ));
}

fn input(ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(1)), ty, SpanId(0))
}

fn comparison(original: u64, instance: u64) -> FnDecl {
    let call = |callee, type_args| {
        Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::Call {
                callee: id(callee),
                type_args,
                args: vec![input(Ty::Bool)],
            },
        )
    };
    let mut caller = original_fn_for_comparison();
    caller.body = Body::Stmts(Block::new(vec![
        Stmt {
            span: SpanId(0),
            kind: StmtKind::Assert {
                expr: Expr::binary(
                    BinOp::Eq,
                    call(original, vec![Ty::Bool]),
                    call(instance, vec![]),
                    Ty::Bool,
                    SpanId(0),
                ),
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
    ]));
    caller
}

fn original_fn_for_comparison() -> FnDecl {
    let mut caller = original();
    caller.id = id(99);
    caller.mode = Mode::Proof;
    caller.type_params.clear();
    caller.locals[0].ty = Ty::Unit;
    caller.locals[1].ty = Ty::Bool;
    caller
}

fn compare_definitions(krate: &VcCrate, shared: bool) {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let vcs = vcgen::generate(krate);
    let vcgen::FnVcs::Checks(checks) = vcs.get(id(99)).unwrap() else {
        panic!("{vcs:?}");
    };
    assert_eq!(checks.len(), 1);
    assert_eq!(
        checks[0].query.goal == vcgen::term::Term::Bool(true),
        shared
    );
    #[cfg(feature = "solve")]
    {
        let verdict = solve::check(
            &checks[0].query,
            "instance body identity",
            &solve::Limits::default(),
        );
        assert!(
            if shared {
                matches!(verdict, solve::Verdict::Proved { .. })
            } else {
                matches!(verdict, solve::Verdict::Refuted { .. })
            },
            "{verdict:?}"
        );
    }
}

#[test]
fn matching_signatures_do_not_authorize_a_different_instance_body() {
    let mut krate = source();
    krate.fns[0].body = Body::Spec(input(Ty::Param(0)));
    krate.fns[1].body = Body::Spec(input(Ty::Bool));
    krate.fns.push(comparison(1, 2));
    compare_definitions(&krate, true);
    krate.fns[1].body = Body::Spec(input(Ty::Bool).not(SpanId(0)));
    compare_definitions(&krate, false);
}

#[test]
fn invalid_nested_specializations_cannot_authorize_their_callers() {
    let mut krate = source();
    krate.fns[0].body = Body::Spec(input(Ty::Param(0)));
    krate.fns[1].body = Body::Spec(input(Ty::Bool));
    let mut outer = original();
    outer.id = id(3);
    outer.body = Body::Spec(Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Call {
            callee: id(1),
            type_args: vec![Ty::Param(0)],
            args: vec![input(Ty::Param(0))],
        },
    ));
    let mut instance = krate.fns[1].clone();
    instance.id = id(4);
    instance.attrs.instance.as_mut().unwrap().declaration = outer.id;
    instance.body = Body::Spec(Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: id(2),
            type_args: vec![],
            args: vec![input(Ty::Bool)],
        },
    ));
    krate.fns.extend([outer, instance]);
    krate.fns.push(comparison(3, 4));
    compare_definitions(&krate, true);
    krate.fns[1].body = Body::Spec(input(Ty::Bool).not(SpanId(0)));
    compare_definitions(&krate, false);
}

#[test]
fn matching_recursive_instances_keep_the_original_group_identity() {
    let mut original = original();
    original.locals.push(local(Ty::nat(), LocalKind::Param));
    original.params.push(LocalId(2));
    let body = |callee, type_args, value_type: Ty| {
        let n = Expr::read(Place::local(LocalId(2)), Ty::nat(), SpanId(0));
        let zero = Expr::int_lit(0, Ty::nat(), SpanId(0));
        let one = Expr::int_lit(1, Ty::nat(), SpanId(0));
        let next = Expr::binary(BinOp::Sub, n.clone(), one, Ty::int(), SpanId(0)).cast(
            CastKind::As,
            Ty::nat(),
            SpanId(0),
        );
        Expr::new(
            value_type.clone(),
            SpanId(0),
            ExprKind::If {
                cond: Box::new(Expr::binary(BinOp::Eq, n, zero, Ty::Bool, SpanId(0))),
                then_expr: Box::new(input(value_type.clone())),
                else_expr: Box::new(Expr::new(
                    value_type.clone(),
                    SpanId(0),
                    ExprKind::Call {
                        callee: id(callee),
                        type_args,
                        args: vec![input(value_type), next],
                    },
                )),
            },
        )
    };
    original.body = Body::Spec(body(1, vec![Ty::Param(0)], Ty::Param(0)));
    original.decreases = vec![Expr::read(Place::local(LocalId(2)), Ty::nat(), SpanId(0))];
    let mut instance = original.clone();
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
    instance.body = Body::Spec(body(2, vec![], Ty::Bool));
    let call = |callee, type_args| {
        Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::Call {
                callee: id(callee),
                type_args,
                args: vec![input(Ty::Bool), Expr::int_lit(0, Ty::nat(), SpanId(0))],
            },
        )
    };
    let mut caller = original_fn_for_comparison();
    caller.body = Body::Stmts(Block::new(vec![
        Stmt {
            span: SpanId(0),
            kind: StmtKind::Assert {
                expr: Expr::binary(
                    BinOp::Eq,
                    call(1, vec![Ty::Bool]),
                    call(2, vec![]),
                    Ty::Bool,
                    SpanId(0),
                ),
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
    ]));
    let mut krate = VcCrate::new("recursive native identity");
    krate.fns = vec![original, instance, caller];
    krate.rec_groups.push(RecGroup {
        members: vec![(id(1), 1)],
    });
    compare_definitions(&krate, true);
    krate.fns[1].body = Body::Spec(input(Ty::Bool).not(SpanId(0)));
    compare_definitions(&krate, false);
}

// Calls to a recursive group must be rejected beneath a quantifier or choice,
// including a validated zero-type-argument instance alias.
fn quantified_recursion(choose: bool, through_instance: bool) -> VcCrate {
    let mut declaration = original();
    declaration.type_params.clear();
    let result = if choose { Ty::nat() } else { Ty::Bool };
    declaration.locals = vec![
        local(result.clone(), LocalKind::Return),
        local(Ty::nat(), LocalKind::Param),
        local(Ty::nat(), LocalKind::Bound),
    ];
    let n = input(Ty::nat());
    let zero = Expr::int_lit(0, Ty::nat(), SpanId(0));
    let next = Expr::binary(
        BinOp::Sub,
        n.clone(),
        Expr::int_lit(1, Ty::nat(), SpanId(0)),
        Ty::int(),
        SpanId(0),
    )
    .cast(CastKind::As, Ty::nat(), SpanId(0));
    let recursive = Expr::new(
        result.clone(),
        SpanId(0),
        ExprKind::Call {
            callee: id(if through_instance { 2 } else { 1 }),
            type_args: vec![],
            args: vec![next],
        },
    );
    let binding = vec![(LocalId(2), Ty::nat())];
    let trigger = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: id(3),
            type_args: vec![],
            args: vec![Expr::read(Place::local(LocalId(2)), Ty::nat(), SpanId(0))],
        },
    );
    let expression = if choose {
        Expr::new(
            Ty::nat(),
            SpanId(0),
            ExprKind::Choose {
                vars: binding,
                triggers: vec![vec![trigger]],
                cond: Box::new(Expr::binary(
                    BinOp::Ge,
                    recursive,
                    zero.clone(),
                    Ty::Bool,
                    SpanId(0),
                )),
                result: Box::new(Expr::read(Place::local(LocalId(2)), Ty::nat(), SpanId(0))),
            },
        )
    } else {
        Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::Quant {
                kind: QuantKind::Forall,
                vars: binding,
                triggers: vec![vec![trigger]],
                body: Box::new(recursive),
            },
        )
    };
    declaration.body = Body::Spec(Expr::new(
        result,
        SpanId(0),
        ExprKind::If {
            cond: Box::new(Expr::binary(
                BinOp::Eq,
                n.clone(),
                zero.clone(),
                Ty::Bool,
                SpanId(0),
            )),
            then_expr: Box::new(if choose {
                zero
            } else {
                Expr::bool_lit(true, SpanId(0))
            }),
            else_expr: Box::new(expression),
        },
    ));
    declaration.decreases = vec![n];
    let mut instance = declaration.clone();
    instance.id = id(2);
    instance.role = FnRole::Instance;
    instance.attrs.instance = Some(GenericInstance {
        declaration: id(1),
        type_args: vec![],
    });
    let mut predicate = original();
    predicate.id = id(3);
    predicate.type_params.clear();
    predicate.locals = vec![
        local(Ty::Bool, LocalKind::Return),
        local(Ty::nat(), LocalKind::Param),
    ];
    let mut krate = VcCrate::new("recursive identity inside binders");
    krate.fns = vec![declaration, instance, predicate];
    krate.rec_groups.push(RecGroup {
        members: vec![(id(1), 1)],
    });
    krate
}

#[test]
fn recursive_instance_aliases_do_not_bypass_quantifier_or_choice_refusal() {
    for choose in [false, true] {
        for through_instance in [false, true] {
            let krate = quantified_recursion(choose, through_instance);
            assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
            let vcs = vcgen::generate(&krate);
            assert!(
                matches!(vcs.get(id(1)), Some(vcgen::FnVcs::Refused(problem))
                if problem.tag == "quantifier-recursion"),
                "choose={choose} alias={through_instance}: {vcs:?}"
            );
        }
    }
}

#[test]
fn unrelated_instance_aliases_under_binders_are_not_recursive() {
    for choose in [false, true] {
        let mut krate = quantified_recursion(choose, true);
        let mut unrelated = krate.fns[1].clone();
        unrelated.id = id(4);
        unrelated.role = FnRole::Item;
        unrelated.attrs.instance = None;
        unrelated.decreases.clear();
        unrelated.body = Body::Spec(if choose {
            Expr::int_lit(0, Ty::nat(), SpanId(0))
        } else {
            Expr::bool_lit(false, SpanId(0))
        });
        krate.fns[1].attrs.instance.as_mut().unwrap().declaration = unrelated.id;
        krate.fns[1].body = unrelated.body.clone();
        krate.fns[1].decreases.clear();
        krate.fns.push(unrelated);
        assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
        let vcs = vcgen::generate(&krate);
        assert!(
            matches!(vcs.get(id(1)), Some(vcgen::FnVcs::Checks(_))),
            "choose={choose}: {vcs:?}"
        );
    }
}
