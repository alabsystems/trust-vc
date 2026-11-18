//! Executable constant freshness, stable globals and independently checked bodies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
use super::*;

fn value(id: u64, kind: FnKind, body: i128, promised: Option<i128>) -> FnDecl {
    let mut f = Fb::new(id, "same_display_name", Mode::Exec, Ty::uint(8));
    f.decl.kind = kind;
    if let Some(promised) = promised {
        let ret = f.rd(f.decl.ret);
        let promised = f.lit(promised, Ty::uint(8));
        let eq = f.cmp(BinOp::Eq, ret, promised);
        f.ensures(eq);
    }
    let literal = f.lit(body, Ty::uint(8));
    let ret = f.ret(Some(literal));
    f.body(vec![ret])
}

fn two_reads(kind: FnKind, second_id: u64, expect_equal: bool) -> VcCrate {
    let first = value(1, kind, 7, None);
    let mut f = Fb::new(3, "consumer", Mode::Exec, Ty::Unit);
    let x = f.let_local("first", Ty::uint(8));
    let y = f.let_local("second", Ty::uint(8));
    let a = f.let_stmt(x, None);
    let b = f.let_stmt(y, None);
    let cx = f.call_stmt(fn_id(1), vec![], Some(Place::local(x)));
    let cy = f.call_stmt(fn_id(second_id), vec![], Some(Place::local(y)));
    let left = f.rd(x);
    let right = f.rd(y);
    let goal = f.cmp(
        if expect_equal { BinOp::Eq } else { BinOp::Ne },
        left,
        right,
    );
    let assertion = f.assert(goal);
    let ret = f.ret(None);
    let mut declarations = vec![first];
    if second_id != 1 {
        declarations.push(value(second_id, kind, 7, None));
    }
    declarations.push(f.body(vec![a, b, cx, cy, assertion, ret]));
    krate(declarations)
}

#[test]
fn executable_constants_are_fresh_and_statics_are_stable_without_body_equations() {
    let exec = FnKind::Constant(ConstMode::Exec);
    for equal in [true, false] {
        assert_eq!(verdicts(&checks_of(&two_reads(exec, 1, equal), 3)), "R");
    }
    assert_eq!(
        verdicts(&checks_of(&two_reads(FnKind::Static, 1, true), 3)),
        "P"
    );
    assert_eq!(
        verdicts(&checks_of(&two_reads(FnKind::Static, 1, false), 3)),
        "R"
    );
    // Two declarations with equal names and initializers have independent
    // global identities; no equality OR disequality follows from their bodies.
    for equal in [true, false] {
        assert_eq!(
            verdicts(&checks_of(&two_reads(FnKind::Static, 2, equal), 3)),
            "R"
        );
    }
}

#[test]
fn initializer_ensures_are_checked_and_only_the_contract_is_available_to_readers() {
    for kind in [FnKind::Constant(ConstMode::Exec), FnKind::Static] {
        for (body, outcome) in [(7, "P"), (8, "R")] {
            let declaration = value(1, kind, body, Some(7));
            let mut f = Fb::new(3, "consumer", Mode::Exec, Ty::Unit);
            let x = f.let_local("read", Ty::uint(8));
            let declare = f.let_stmt(x, None);
            let call = f.call_stmt(fn_id(1), vec![], Some(Place::local(x)));
            let result = f.rd(x);
            let number = f.lit(7, Ty::uint(8));
            let goal = f.cmp(BinOp::Eq, result, number);
            let assertion = f.assert(goal);
            let ret = f.ret(None);
            let source = krate(vec![
                declaration,
                f.body(vec![declare, call, assertion, ret]),
            ]);
            assert_eq!(verdicts(&checks_of(&source, 1)), outcome);
            assert_eq!(verdicts(&checks_of(&source, 3)), "P");
        }
        let mut source = two_reads(kind, 1, true);
        let Body::Stmts(body) = &mut source.fns.last_mut().unwrap().body else {
            unreachable!()
        };
        let StmtKind::Assert { expr, .. } = &mut body.stmts[4].kind else {
            unreachable!()
        };
        let ExprKind::Binary { rhs, .. } = &mut expr.kind else {
            unreachable!()
        };
        *rhs = Box::new(Expr::int_lit(7, Ty::uint(8), SpanId(0)));
        // An initializer returning 7 does not export the equation read()==7.
        assert_eq!(verdicts(&checks_of(&source, 3)), "R");
    }
}

#[test]
fn static_storage_rejects_owned_generic_and_mutable_reference_carriers() {
    for ty in [
        Ty::Param(0),
        Ty::MutRef(Box::new(Ty::uint(8))),
        Ty::Ref {
            mutable: true,
            inner: Box::new(Ty::uint(8)),
        },
    ] {
        let mut static_decl = value(1, FnKind::Static, 7, None);
        if matches!(ty, Ty::Param(_)) {
            static_decl.type_params = vec!["T".into()];
        }
        static_decl.locals[0].ty = ty;
        static_decl.body = Body::None;
        static_decl.attrs.external_body = true;
        assert!(!check_crate(&krate(vec![static_decl])).is_empty());
    }
    let mut source = two_reads(FnKind::Static, 1, true);
    source.fns[0].params = vec![source.fns[0].ret];
    assert!(!check_crate(&source).is_empty());
}

#[test]
fn executable_values_do_not_acquire_spec_or_dual_bodies() {
    for kind in [FnKind::Constant(ConstMode::Exec), FnKind::Static] {
        for body in [
            Body::Spec(Expr::int_lit(7, Ty::uint(8), SpanId(0))),
            Body::Constant(Expr::int_lit(7, Ty::uint(8), SpanId(0))),
        ] {
            let mut declaration = value(1, kind, 7, None);
            declaration.body = body;
            assert!(!check_crate(&krate(vec![declaration])).is_empty());
        }
        let mut source = two_reads(kind, 1, true);
        let consumer = source.fns.last_mut().unwrap();
        consumer.mode = Mode::Proof;
        for local in &mut consumer.locals {
            local.mode = Mode::Spec;
        }
        assert!(!check_crate(&source).is_empty());
    }
}

#[test]
fn static_identity_and_type_membership_survive_isolated_loop_queries() {
    for false_goal in [false, true] {
        let declaration = value(1, FnKind::Static, 7, None);
        let mut f = Fb::new(3, "loop_consumer", Mode::Exec, Ty::Unit);
        // Seed the per-query static identity before entering an isolated loop.
        // Its cached value must not lose type membership when facts are cut.
        let outer = f.let_local("outer", Ty::uint(8));
        let declare_outer = f.let_stmt(outer, None);
        let read_outer = f.call_stmt(fn_id(1), vec![], Some(Place::local(outer)));
        let x = f.let_local("x", Ty::uint(8));
        let y = f.let_local("y", Ty::uint(8));
        let dx = f.let_stmt(x, None);
        let dy = f.let_stmt(y, None);
        let cx = f.call_stmt(fn_id(1), vec![], Some(Place::local(x)));
        let cy = f.call_stmt(fn_id(1), vec![], Some(Place::local(y)));
        let rx = f.rd(x);
        let ry = f.rd(y);
        let equal = f.cmp(BinOp::Eq, rx, ry);
        let eq_assertion = f.assert(equal);
        let rx = f.rd(x);
        let bound = f.lit(255, Ty::uint(8));
        let bounded = f.cmp(if false_goal { BinOp::Gt } else { BinOp::Le }, rx, bound);
        let type_assertion = f.assert(bounded);
        let exit = f.brk(0);
        let zero = f.lit(0, Ty::int());
        let lp = f.looped(
            0,
            None,
            vec![],
            vec![zero],
            vec![dx, dy, cx, cy, eq_assertion, type_assertion, exit],
            false,
        );
        let ret = f.ret(None);
        let source = krate(vec![
            declaration,
            f.body(vec![declare_outer, read_outer, lp, ret]),
        ]);
        let checks = checks_of(&source, 3);
        let assertions = checks
            .iter()
            .filter(|check| matches!(check.kind, CheckKind::Assert { .. }))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(verdicts(&assertions), if false_goal { "PR" } else { "PP" });
    }
}

#[test]
fn cyclic_static_contracts_and_false_initializers_do_not_provide_a_proof() {
    let mut source = two_reads(FnKind::Static, 1, true);
    source.rec_groups.push(RecGroup {
        members: vec![(fn_id(1), 1)],
    });
    assert!(!check_crate(&source).is_empty());
    let mut source = krate(vec![value(1, FnKind::Static, 7, Some(8))]);
    assert_eq!(verdicts(&checks_of(&source, 1)), "R");
    // Changing that initializer's contract cannot turn the global into a
    // mathematical initializer equation in a different declaration.
    source.fns[0].ensures.clear();
    assert!(check_crate(&source).is_empty());
}

fn initializer_reading(id: u64, dependency: u64, false_contract: bool) -> FnDecl {
    let mut f = Fb::new(id, "initializer", Mode::Exec, Ty::uint(8));
    f.decl.kind = FnKind::Static;
    let promised = if false_contract {
        f.tt(false)
    } else {
        let result = f.rd(f.decl.ret);
        let three = f.lit(3, Ty::uint(8));
        f.cmp(BinOp::Eq, result, three)
    };
    f.ensures(promised);
    let result = f.let_local("dependency", Ty::uint(8));
    let declare = f.let_stmt(result, None);
    let call = f.call_stmt(fn_id(dependency), vec![], Some(Place::local(result)));
    let returned = f.rd(result);
    let ret = f.ret(Some(returned));
    f.body(vec![declare, call, ret])
}

fn outside_consumer(target: u64, expected: Option<i128>) -> FnDecl {
    let mut f = Fb::new(3, "outside_consumer", Mode::Exec, Ty::Unit);
    let x = f.let_local("global", Ty::uint(8));
    let declare = f.let_stmt(x, None);
    let read = f.call_stmt(fn_id(target), vec![], Some(Place::local(x)));
    let goal = match expected {
        Some(expected) => {
            let global = f.rd(x);
            let expected = f.lit(expected, Ty::uint(8));
            f.cmp(BinOp::Eq, global, expected)
        }
        None => f.tt(false),
    };
    let claim = f.assert(goal);
    let ret = f.ret(None);
    f.body(vec![declare, read, claim, ret])
}

#[test]
fn mutually_cyclic_statics_cannot_export_false_to_an_outside_consumer_without_rec_groups() {
    let source = krate(vec![
        initializer_reading(1, 2, true),
        initializer_reading(2, 1, true),
        outside_consumer(1, None),
    ]);
    assert!(source.rec_groups.is_empty());
    assert!(check_crate(&source)
        .iter()
        .any(|problem| problem.message.contains("cycle through a Static")));
    // Also defend the read boundary for a direct generator caller that omitted
    // its WF precondition. Ordinary uncovered_cycles already refuses the two
    // initializers; the outside consumer must refuse before assuming ensures.
    let generated = generate(&source);
    for id in [1, 2, 3] {
        assert!(matches!(generated.get(fn_id(id)), Some(FnVcs::Refused(_))));
    }
    let Some(FnVcs::Refused(problem)) = generated.get(fn_id(3)) else {
        unreachable!()
    };
    assert_eq!(problem.tag, "static-read-dependency");
}

#[test]
fn acyclic_static_dependencies_keep_real_postconditions_and_false_twins() {
    for (expected, verdict) in [(3, "P"), (4, "R")] {
        let source = krate(vec![
            initializer_reading(1, 2, false),
            value(2, FnKind::Static, 3, Some(3)),
            outside_consumer(1, Some(expected)),
        ]);
        assert!(check_crate(&source).is_empty());
        assert_eq!(verdicts(&checks_of(&source, 1)), "P");
        assert_eq!(verdicts(&checks_of(&source, 2)), "P");
        assert_eq!(verdicts(&checks_of(&source, 3)), verdict);
    }
}

#[test]
fn missing_and_unchecked_executable_dependencies_cannot_export_static_contracts() {
    for missing in [true, false] {
        let mut declarations = vec![initializer_reading(1, 2, true), outside_consumer(1, None)];
        if !missing {
            let mut unavailable = value(2, FnKind::Function, 3, None);
            unavailable.body = Body::None;
            unavailable.attrs.external_body = false;
            declarations.push(unavailable);
        }
        let source = krate(declarations);
        assert!(check_crate(&source)
            .iter()
            .any(|problem| problem.function == Some(fn_id(1))));
        let generated = generate(&source);
        let Some(FnVcs::Refused(problem)) = generated.get(fn_id(3)) else {
            panic!("{generated:?}");
        };
        assert_eq!(problem.tag, "static-read-dependency");
    }
}

fn generic_statement(mut call: Stmt, arguments: Vec<Ty>) -> Stmt {
    let StmtKind::Call { type_args, .. } = &mut call.kind else {
        unreachable!()
    };
    *type_args = arguments;
    call
}

#[test]
fn closed_abstract_trait_dependency_cannot_export_false_static_ensures() {
    let mut target = Fb::new(2, "abstract_trait_dependency", Mode::Exec, Ty::uint(8));
    target.decl.role = FnRole::TraitDecl;
    target.decl.type_params = vec!["Self".into()];
    let mut initializer = initializer_reading(1, 2, true);
    let Body::Stmts(body) = &mut initializer.body else {
        unreachable!()
    };
    body.stmts[1] = generic_statement(body.stmts[1].clone(), vec![Ty::uint(8)]);
    let source = krate(vec![initializer, target.decl, outside_consumer(1, None)]);
    assert!(source.rec_groups.is_empty());
    assert!(check_crate(&source)
        .iter()
        .any(|problem| problem.function == Some(fn_id(1))));
    let generated = generate(&source);
    let Some(FnVcs::Refused(problem)) = generated.get(fn_id(3)) else {
        panic!("{generated:?}");
    };
    assert_eq!(problem.tag, "static-read-dependency");
    let Some(FnVcs::Refused(initializer)) = generated.get(fn_id(1)) else {
        panic!("{generated:?}");
    };
    assert!(
        initializer.detail.contains("not represented"),
        "{initializer:?}"
    );
    assert!(
        problem.detail.contains("generation was refused"),
        "{problem:?}"
    );
}

// Generic H<T> has an ordinary represented B::<T> trait dispatch. Its checked
// closed native instance H_u8 has no independent proof body or new contract.
fn represented_dispatch(expected: i128) -> VcCrate {
    let mut target = Fb::new(2, "trait_dependency", Mode::Exec, Ty::uint(8));
    target.decl.role = FnRole::TraitDecl;
    target.decl.type_params = vec!["Self".into()];
    let result = target.rd(target.decl.ret);
    let three = target.lit(3, Ty::uint(8));
    let post = target.cmp(BinOp::Eq, result, three);
    target.ensures(post);
    let target = target.decl;
    let mut original = Fb::new(4, "generic_dispatch", Mode::Exec, Ty::uint(8));
    original.decl.type_params = vec!["T".into()];
    original.decl.copy_premises = vec![Ty::Param(0)];
    let result = original.rd(original.decl.ret);
    let three = original.lit(3, Ty::uint(8));
    let post = original.cmp(BinOp::Eq, result, three);
    original.ensures(post);
    let local = original.let_local("result", Ty::uint(8));
    let declare = original.let_stmt(local, None);
    let call = original.call_stmt(fn_id(2), vec![], Some(Place::local(local)));
    let call = generic_statement(call, vec![Ty::Param(0)]);
    let result = original.rd(local);
    let ret = original.ret(Some(result));
    let original = original.body(vec![declare, call, ret]);
    let mut instance = original.clone();
    instance.id = fn_id(5);
    instance.name = "native_closed_dispatch".into();
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    instance.copy_premises = vec![Ty::uint(8)];
    instance.body = Body::None;
    instance.attrs.instance = Some(trust_vc_vcir::GenericInstance {
        declaration: original.id,
        type_args: vec![Ty::uint(8)],
    });
    krate(vec![
        target,
        original,
        instance,
        initializer_reading(1, 5, false),
        outside_consumer(1, Some(expected)),
    ])
}

#[test]
fn represented_param_dispatch_and_checked_closed_instance_keep_false_twins() {
    for (expected, outcome) in [(3, "P"), (4, "R")] {
        let source = represented_dispatch(expected);
        assert!(
            check_crate(&source).is_empty(),
            "{:?}",
            check_crate(&source)
        );
        assert_eq!(verdicts(&checks_of(&source, 4)), "P");
        assert_eq!(verdicts(&checks_of(&source, 1)), "P");
        assert_eq!(verdicts(&checks_of(&source, 3)), outcome);
    }
}

#[test]
fn executable_local_impl_origins_do_not_inherit_the_spec_uf_exclusion() {
    for (expected, outcome) in [(3, "P"), (4, "R")] {
        let mut source = represented_dispatch(expected);
        for declaration in &mut source.fns {
            if [fn_id(4), fn_id(5)].contains(&declaration.id) {
                declaration.attrs.is_trait_method_impl = true;
            }
        }
        assert!(
            check_crate(&source).is_empty(),
            "{:?}",
            check_crate(&source)
        );
        assert_eq!(verdicts(&checks_of(&source, 3)), outcome);
    }
}

#[test]
fn instance_role_or_forged_contracts_cannot_authorize_static_facts() {
    for mutation in 0..10 {
        let mut source = represented_dispatch(3);
        let instance = source
            .fns
            .iter_mut()
            .find(|decl| decl.id == fn_id(5))
            .unwrap();
        match mutation {
            0 => instance.attrs.instance = None,
            1 => instance.ensures[0].expr = Expr::bool_lit(false, SpanId(0)),
            2 => instance.requires.push(Clause {
                expr: Expr::bool_lit(false, SpanId(0)),
                span: SpanId(0),
                attrs: ClauseAttrs::default(),
            }),
            3 => instance.recommends.push(Clause {
                expr: Expr::bool_lit(true, SpanId(0)),
                span: SpanId(0),
                attrs: ClauseAttrs::default(),
            }),
            4 => instance.copy_premises.clear(),
            5 => instance.attrs.instance.as_mut().unwrap().type_args = vec![Ty::Unit],
            6 => instance.attrs.instance.as_mut().unwrap().declaration = fn_id(2),
            7 => instance.attrs.instance.as_mut().unwrap().declaration = fn_id(999),
            8 => instance.unwind = Some(trust_vc_vcir::UnwindSpec::MayUnwind),
            9 => instance
                .decreases
                .push(Expr::int_lit(1, Ty::int(), SpanId(0))),
            _ => unreachable!(),
        }
        let index = source
            .fns
            .iter()
            .position(|decl| decl.id == fn_id(1))
            .unwrap();
        source.fns[index].ensures[0].expr = Expr::bool_lit(false, SpanId(0));
        let index = source
            .fns
            .iter()
            .position(|decl| decl.id == fn_id(3))
            .unwrap();
        source.fns[index] = outside_consumer(1, None);
        assert!(source.rec_groups.is_empty());
        let generated = generate(&source);
        let Some(FnVcs::Refused(problem)) = generated.get(fn_id(3)) else {
            panic!("mutation {mutation}: {generated:?}");
        };
        assert_eq!(problem.tag, "static-read-dependency");
    }
}

#[test]
fn instance_parameter_order_is_semantic_even_for_identically_typed_slots() {
    let mut original = Fb::new(4, "first", Mode::Exec, Ty::uint(8));
    original.decl.type_params = vec!["T".into()];
    let left = original.param("left", Ty::uint(8));
    original.param("right", Ty::uint(8));
    let result = original.rd(original.decl.ret);
    let input = original.rd(left);
    let post = original.cmp(BinOp::Eq, result, input);
    original.ensures(post);
    let input = original.rd(left);
    let ret = original.ret(Some(input));
    let original = original.body(vec![ret]);
    let mut instance = original.clone();
    instance.id = fn_id(5);
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    instance.body = Body::None;
    instance.attrs.instance = Some(trust_vc_vcir::GenericInstance {
        declaration: original.id,
        type_args: vec![Ty::uint(8)],
    });
    let mut initializer = initializer_reading(1, 5, false);
    let Body::Stmts(body) = &mut initializer.body else {
        unreachable!()
    };
    let StmtKind::Call { args, .. } = &mut body.stmts[1].kind else {
        unreachable!()
    };
    *args = vec![
        Expr::int_lit(3, Ty::uint(8), SpanId(0)),
        Expr::int_lit(4, Ty::uint(8), SpanId(0)),
    ];
    for (mutated, expected) in [(false, 3), (false, 4), (true, 3)] {
        let mut instance = instance.clone();
        if mutated {
            instance.params.swap(0, 1);
        }
        let source = krate(vec![
            original.clone(),
            instance,
            initializer.clone(),
            outside_consumer(1, Some(expected)),
        ]);
        if mutated {
            let generated = generate(&source);
            let Some(FnVcs::Refused(problem)) = generated.get(fn_id(3)) else {
                panic!("{generated:?}");
            };
            assert_eq!(problem.tag, "static-read-dependency");
        } else {
            assert!(
                check_crate(&source).is_empty(),
                "{:?}",
                check_crate(&source)
            );
            assert_eq!(
                verdicts(&checks_of(&source, 3)),
                if expected == 3 { "P" } else { "R" }
            );
        }
    }
}

#[test]
fn unexecuted_instance_body_keeps_dependencies_without_rechecking_substituted_dispatch() {
    let mut source = represented_dispatch(3);
    let body = source
        .fns
        .iter()
        .find(|decl| decl.id == fn_id(4))
        .unwrap()
        .body
        .clone();
    let instance = source
        .fns
        .iter_mut()
        .find(|decl| decl.id == fn_id(5))
        .unwrap();
    instance.body = body;
    let Body::Stmts(block) = &mut instance.body else {
        unreachable!()
    };
    block.stmts[1] = generic_statement(block.stmts[1].clone(), vec![Ty::uint(8)]);
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    assert_eq!(verdicts(&checks_of(&source, 3)), "P");
    // Those ignored body edges still matter: an otherwise ignored Static
    // self dependency cannot be hidden behind the instance role.
    let instance = source
        .fns
        .iter_mut()
        .find(|decl| decl.id == fn_id(5))
        .unwrap();
    let Body::Stmts(block) = &mut instance.body else {
        unreachable!()
    };
    let StmtKind::Call {
        callee, type_args, ..
    } = &mut block.stmts[1].kind
    else {
        unreachable!()
    };
    *callee = fn_id(1);
    type_args.clear();
    assert!(!check_crate(&source).is_empty());
    let generated = generate(&source);
    assert!(matches!(generated.get(fn_id(3)), Some(FnVcs::Refused(_))));
}

#[test]
fn actual_refused_helper_generation_blocks_static_facts_without_rec_groups() {
    let mut helper = initializer_reading(2, 4, true);
    helper.kind = FnKind::Function;
    let Body::Stmts(body) = &mut helper.body else {
        unreachable!()
    };
    assert!(matches!(body.stmts.remove(0).kind, StmtKind::Let { .. }));
    let mut source = krate(vec![
        initializer_reading(1, 2, true),
        helper,
        outside_consumer(1, None),
        value(4, FnKind::Function, 3, None),
    ]);
    assert!(source.rec_groups.is_empty());
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    for reverse in [false, true] {
        if reverse {
            source.fns.reverse();
        }
        let session = trust_vc_vcir::vcgen::GenerationSession::new(&source).unwrap();
        let generated = session.vcs();
        let Some(FnVcs::Refused(helper)) = generated.get(fn_id(2)) else {
            panic!("{generated:?}");
        };
        assert_eq!(helper.tag, "vcgen-internal");
        assert_eq!(helper.detail, "assignment to undeclared local");
        for id in [1, 3] {
            let Some(FnVcs::Refused(problem)) = generated.get(fn_id(id)) else {
                panic!("{generated:?}");
            };
            assert_eq!(problem.tag, "static-read-dependency");
            assert!(
                problem.detail.contains("generation was refused"),
                "{problem:?}"
            );
        }
        assert_eq!(
            generated.fns.iter().map(|(id, _)| *id).collect::<Vec<_>>(),
            source.fns.iter().map(|decl| decl.id).collect::<Vec<_>>()
        );
    }
}

#[test]
fn recommendations_borrow_the_live_static_context_without_changing_normal_results() {
    let declaration = value(1, FnKind::Static, 0, Some(0));
    let mut domain = Fb::new(4, "positive_domain", Mode::Spec, Ty::Bool);
    let input = domain.param("input", Ty::uint(8));
    let input = domain.rd(input);
    let zero = domain.lit(0, Ty::uint(8));
    let condition = domain.cmp(BinOp::Gt, input, zero);
    let recommendation = domain.clause(condition);
    domain.decl.recommends.push(recommendation);
    let truth = domain.tt(true);
    let domain = domain.spec_body(truth);
    let mut f = Fb::new(3, "failed_consumer", Mode::Exec, Ty::Unit);
    let local = f.let_local("global", Ty::uint(8));
    let declare = f.let_stmt(local, None);
    let read = f.call_stmt(fn_id(1), vec![], Some(Place::local(local)));
    let arg = f.rd(local);
    let call = f.call(fn_id(4), vec![arg], Ty::Bool);
    let domain_use = f.assert(call);
    let false_goal = f.tt(false);
    let failure = f.assert(false_goal);
    let ret = f.ret(None);
    let source = krate(vec![
        f.body(vec![declare, read, domain_use, failure, ret]),
        declaration,
        domain,
    ]);
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    let session = trust_vc_vcir::vcgen::GenerationSession::new(&source).unwrap();
    let normal = session.vcs().clone();
    let checks = session.recommendations(fn_id(3)).unwrap();
    let diagnostic = checks
        .into_iter()
        .filter(|check| matches!(check.kind, CheckKind::Recommendation { .. }))
        .collect::<Vec<_>>();
    assert!(!diagnostic.is_empty());
    assert!(verdicts(&diagnostic).contains('R'));
    assert_eq!(session.vcs(), &normal);
}
