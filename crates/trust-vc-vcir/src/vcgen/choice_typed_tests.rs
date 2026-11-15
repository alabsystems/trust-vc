// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::closed_templates::tests::{application, source};
use super::super::spec::Tables;
use super::super::type_encoding::TypeArgument;
use super::*;
use crate::{AdtDecl, AdtId, AdtKind, DefHash, VcCrate};

fn owner() -> FnId {
    FnId(DefHash::new(57, 1))
}

fn choice(ty: Ty) -> Expr {
    let value = Expr::read(Place::local(LocalId(7)), ty.clone(), SpanId(0));
    let predicate = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: owner(),
            type_args: vec![ty.clone()],
            args: vec![value.clone()],
        },
    );
    Expr::new(
        ty.clone(),
        SpanId(0),
        ExprKind::Choose {
            vars: vec![(LocalId(7), ty)],
            triggers: vec![vec![predicate.clone()]],
            cond: Box::new(predicate),
            result: Box::new(value),
        },
    )
}

#[test]
fn actual_closed_choice_translation_admits_boxed_predicate_without_definition_facts() {
    let krate = source();
    assert!(crate::check_crate(&krate).is_empty());
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let mut tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    let result = tr
        .expr(&choice(Ty::Int(IntRange::U(8))))
        .unwrap()
        .into_leaf()
        .unwrap();
    let Term::Call { name, args, sort } = result else {
        panic!("registered choice application")
    };
    assert_eq!(sort, Sort::Int);
    let registry = ctx.quants.borrow();
    let (params, ret) = registry.signature(&name).expect("actual registered choice");
    assert_eq!(ret, Sort::Int);
    assert_eq!(params.len(), args.len());
    assert!(params.iter().zip(&args).all(|(a, b)| *a == b.sort()));
    assert!(
        tr.checks.is_empty(),
        "template admission creates no assertion or witness check"
    );
    assert!(
        matches!(krate.fns[0].body, crate::Body::None),
        "the predicate is genuinely uninterpreted; admission supplies no predicate definition"
    );
}

#[test]
fn admission_uses_the_posttranslation_vocabulary_not_an_earlier_recipe_snapshot() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let old = super::super::closed_templates::Vocabulary::new(
        &ctx,
        &tables.functions,
        &tables.sigs,
        &mut |_| true,
    )
    .unwrap();
    let predicate = application(
        &ctx,
        &tables,
        Ty::Int(IntRange::U(8)),
        Term::var("qb", Sort::Int),
    );
    assert!(
        !old.check(&quant::Registry::default(), &[&predicate], &[], &mut |_| {
            true
        }),
        "the closed u8 recipe was not registered in the pretranslation snapshot"
    );
    let reads = Reads::default();
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert!(tr
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_ok());
}

#[test]
fn complete_condition_values_triggers_and_actual_hole_arguments_are_checked_together() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let predicate = application(&ctx, &tables, Ty::nat(), Term::var("qb", Sort::Int));
    let reads = Reads::default();
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    let bound = vec![("qb".into(), LeafTy::Int(IntRange::Nat))];
    let holes = vec![("qh".into(), LeafTy::Int(IntRange::Nat))];
    let value = Term::var("qb", Sort::Int);
    let actual = Term::Int(3);
    let triggers = vec![vec![predicate.clone()]];
    assert!(tr
        .check_choice_template(
            &bound,
            &holes,
            &predicate,
            &[value.clone()],
            &triggers,
            &[actual],
            SpanId(0)
        )
        .is_ok());
    let forged = Term::call(
        "same_surface_without_registered_signature",
        vec![],
        Sort::Bool,
    );
    assert!(tr
        .check_choice_template(
            &bound,
            &holes,
            &forged,
            &[value.clone()],
            &triggers,
            &[],
            SpanId(0)
        )
        .is_err());
    assert!(tr
        .check_choice_template(
            &bound,
            &holes,
            &predicate,
            &[forged.clone()],
            &triggers,
            &[],
            SpanId(0)
        )
        .is_err());
    assert!(tr
        .check_choice_template(
            &bound,
            &holes,
            &predicate,
            &[value.clone()],
            &[vec![forged.clone()]],
            &[],
            SpanId(0)
        )
        .is_err());
    assert!(tr
        .check_choice_template(
            &bound,
            &holes,
            &predicate,
            &[value],
            &triggers,
            &[forged],
            SpanId(0)
        )
        .is_err());
}

#[test]
fn closed_pairs_call_result_arity_and_shared_variable_sorts_refuse_counterfeits() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let predicate = application(&ctx, &tables, Ty::nat(), Term::var("qb", Sort::Int));
    let Term::Call { name, args, .. } = &predicate else {
        panic!("actual generic call")
    };
    let reads = Reads::default();
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    let mut wrong_pair = args.clone();
    wrong_pair[0] = Term::call("counterfeit_decoration", vec![], Sort::Decoration);
    let mut missing = args.clone();
    missing.remove(0);
    let mut swapped = args.clone();
    swapped.swap(0, 1);
    let variants = [
        Term::call(name, wrong_pair, Sort::Bool),
        Term::call(name, missing, Sort::Bool),
        Term::call(name, swapped, Sort::Bool),
        Term::call(name, args.clone(), Sort::Int),
    ];
    for other in variants {
        assert!(tr
            .check_choice_template(&[], &[], &other, &[], &[], &[], SpanId(0))
            .is_err());
    }
    assert!(tr
        .check_choice_template(
            &[("qb".into(), LeafTy::Int(IntRange::Nat))],
            &[("qb".into(), LeafTy::Bool)],
            &predicate,
            &[],
            &[],
            &[],
            SpanId(0)
        )
        .is_err());
    assert!(tr
        .check_choice_template(
            &[],
            &[],
            &predicate,
            &[],
            &[],
            &[Term::var("qb", Sort::Bool)],
            SpanId(0)
        )
        .is_err());
}

#[test]
fn open_inline_environment_cannot_be_licensed_by_closed_looking_type_names() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let predicate = application(&ctx, &tables, Ty::nat(), Term::Int(1));
    let valid = ctx
        .type_argument(&Ty::nat(), &TypeEnv::default(), SpanId(0))
        .unwrap();
    let reads = Reads {
        types: TypeEnv::new(owner(), vec![valid]),
        ..Reads::default()
    };
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert!(tr
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_ok());
    let forged = TypeArgument::new(
        Term::call("nil_lookalike", vec![], Sort::Decoration),
        Term::call("nat_lookalike", vec![], Sort::TypeId),
    )
    .unwrap();
    let reads = Reads {
        types: TypeEnv::new(owner(), vec![forged]),
        ..Reads::default()
    };
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert!(tr
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_err());
    let open = TypeArgument::new(
        Term::var("open_dec", Sort::Decoration),
        Term::var("open_type", Sort::TypeId),
    )
    .unwrap();
    let reads = Reads {
        types: TypeEnv::new(owner(), vec![open]),
        ..Reads::default()
    };
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert!(tr
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_err());
}

#[test]
fn abstract_poly_domains_and_results_still_refuse() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let mut tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert_eq!(
        tr.expr(&choice(Ty::Param(0))).unwrap_err().tag,
        "generic-choice"
    );
    assert!(tr
        .check_choice_template(
            &[("qb".into(), LeafTy::Poly(0))],
            &[],
            &Term::Bool(true),
            &[],
            &[],
            &[],
            SpanId(0)
        )
        .is_err());
    assert!(tr
        .check_choice_template(
            &[],
            &[],
            &Term::Bool(true),
            &[Term::var("abstract_result", Sort::Poly)],
            &[],
            &[],
            SpanId(0)
        )
        .is_err());
}

#[test]
fn two_admitted_nominals_keep_distinct_sorts_in_values_triggers_and_holes() {
    let mut krate: VcCrate = source();
    for number in [21, 22] {
        krate.adts.push(AdtDecl {
            id: AdtId(DefHash::new(57, number)),
            name: format!("N{number}"),
            type_params: vec![],
            span: SpanId(0),
            kind: AdtKind::Opaque,
            variants: vec![],
        });
    }
    assert!(crate::check_crate(&krate).is_empty());
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let mut terms = Vec::new();
    for (index, number) in [21, 22].into_iter().enumerate() {
        let ty = Ty::Adt(AdtId(DefHash::new(57, number)), vec![]);
        let Shape::Leaf(leaf) = ctx.shape(&ty, None, SpanId(0)).unwrap() else {
            panic!("opaque scalar")
        };
        terms.push((Term::var(format!("n{index}"), leaf.sort()), leaf, ty));
    }
    assert_ne!(terms[0].0.sort(), terms[1].0.sort());
    let predicate = application(&ctx, &tables, terms[0].2.clone(), terms[0].0.clone());
    let reads = Reads::default();
    let tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    assert!(tr
        .check_choice_template(
            &[("n0".into(), terms[0].1)],
            &[],
            &predicate,
            &[terms[0].0.clone()],
            &[vec![predicate.clone()]],
            &[],
            SpanId(0)
        )
        .is_ok());
    let cross = Term::eq(terms[0].0.clone(), terms[1].0.clone());
    assert!(tr
        .check_choice_template(&[], &[], &cross, &[], &[], &[], SpanId(0))
        .is_err());
    assert!(tr
        .check_choice_template(
            &[("n0".into(), terms[0].1)],
            &[("n0".into(), terms[1].1)],
            &predicate,
            &[],
            &[],
            &[],
            SpanId(0)
        )
        .is_err());
}

#[test]
fn repeated_choice_admission_spends_the_same_inline_grant_without_refill() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let predicate = application(&ctx, &tables, Ty::nat(), Term::var("qb", Sort::Int));
    let reads = Reads::default();
    let mut measured = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    measured.inline_stack.push(owner());
    let before = measured.inline_work.get();
    assert!(measured
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_ok());
    let cost = before - measured.inline_work.get();
    assert!(cost > 0);
    let mut repeated = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    repeated.inline_stack.push(owner());
    repeated.inline_work.set(cost + cost / 2);
    assert!(repeated
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_ok());
    assert!(repeated
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_err());
    assert!(repeated.inline_work.get() <= cost / 2);
    assert!(repeated
        .check_choice_template(&[], &[], &predicate, &[], &[], &[], SpanId(0))
        .is_err());
}

#[test]
fn unfunded_large_hole_name_declines_before_copy_or_vocabulary_capture() {
    let krate = source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let mut tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    tr.inline_stack.push(owner());
    tr.inline_work.set(64);
    let functions = ctx.type_functions();
    let error = tr
        .check_choice_template(
            &[],
            &[("h".repeat(4096), LeafTy::Bool)],
            &Term::Bool(true),
            &[],
            &[],
            &[],
            SpanId(0),
        )
        .unwrap_err();
    assert_eq!(error.detail, "typed choice template work exhausted");
    assert_eq!(
        ctx.type_functions(),
        functions,
        "failed admission mutates no encoding vocabulary"
    );
    assert_eq!(
        tr.inline_work.get(),
        63,
        "unfunded name is never copied then charged"
    );
}
