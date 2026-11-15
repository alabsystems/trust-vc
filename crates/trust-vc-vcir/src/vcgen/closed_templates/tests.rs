// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::expr::{Reads, Tr};
use super::super::spec::Tables;
use super::super::type_encoding::TypeEnv;
use super::super::val::Val;
use super::*;
use crate::{
    Body, DefHash, Expr, ExprKind, FnAttrs, FnDecl, FnKind, FnRole, LocalDecl, LocalId, LocalKind,
    Mode, Place, SpanId, Ty, VcCrate,
};

pub(in crate::vcgen) fn source() -> VcCrate {
    let function = |number, parameter, generic| FnDecl {
        id: FnId(DefHash::new(57, number)),
        name: format!("p{number}"),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: if generic { vec!["A".into()] } else { vec![] },
        locals: vec![
            LocalDecl {
                name: "result".into(),
                ty: Ty::Bool,
                mode: Mode::Spec,
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(0),
            },
            LocalDecl {
                name: "value".into(),
                ty: parameter,
                mode: Mode::Spec,
                mutable: false,
                kind: LocalKind::Param,
                span: SpanId(0),
            },
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
    };
    let mut krate = VcCrate::new("closed concrete templates");
    krate.fns.push(function(1, Ty::Param(0), true));
    krate.fns.push(function(2, Ty::int(), false));
    krate
}

pub(in crate::vcgen) fn application(ctx: &Ctx<'_>, tables: &Tables, ty: Ty, value: Term) -> Term {
    let reads = Reads {
        read: [(LocalId(1), Val::Leaf(value))].into_iter().collect(),
        old: HashMap::new(),
        types: TypeEnv::default(),
    };
    let expr = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: FnId(DefHash::new(57, 1)),
            type_args: vec![ty.clone()],
            args: vec![Expr::read(Place::local(LocalId(1)), ty, SpanId(0))],
        },
    );
    Tr::new(ctx, &tables.sigs, &tables.functions, &reads)
        .expr(&expr)
        .unwrap()
        .into_leaf()
        .unwrap()
}

#[test]
fn concrete_boxed_templates_use_actual_registered_signatures_and_recipes() {
    let source = source();
    assert!(crate::check_crate(&source).is_empty());
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::var("x", Sort::Int));
    let functions = ctx.type_functions();
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    assert!(vocabulary.check(
        &Registry::default(),
        &[&term],
        &[("x".into(), LeafTy::Int(crate::IntRange::Nat))],
        &mut |_| true
    ));
    assert_eq!(
        functions,
        ctx.type_functions(),
        "checking adds no vocabulary, predicate or material call"
    );
}

#[test]
fn malformed_call_results_tags_arity_and_free_type_variables_refuse() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::var("x", Sort::Int));
    let Term::Call { name, args, .. } = term else {
        panic!("actual SF application");
    };
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let mut variants = vec![Term::call(name.clone(), args.clone(), Sort::Int)];
    let mut wrong = args.clone();
    wrong.swap(0, 1);
    variants.push(Term::call(name.clone(), wrong, Sort::Bool));
    let mut missing = args.clone();
    missing.remove(0);
    variants.push(Term::call(name.clone(), missing, Sort::Bool));
    let mut forged = args.clone();
    forged[0] = Term::call("ty_dec_counterfeit", vec![], Sort::Decoration);
    variants.push(Term::call(name.clone(), forged, Sort::Bool));
    let mut free = args;
    free[1] = Term::var("unbound_type", Sort::TypeId);
    variants.push(Term::call(name, free, Sort::Bool));
    for term in variants {
        assert!(!vocabulary.check(&registry, &[&term], &[], &mut |_| true));
    }
}

#[test]
fn repeated_names_and_mismatched_binder_sorts_do_not_survive_collection() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::var("x", Sort::Int));
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let both = Term::and([term.clone(), Term::var("x", Sort::Bool)]);
    assert!(!vocabulary.check(&Registry::default(), &[&both], &[], &mut |_| true));
    assert!(!vocabulary.check(
        &Registry::default(),
        &[&term],
        &[("x".into(), LeafTy::Bool)],
        &mut |_| true
    ));
    assert!(!vocabulary.check(&Registry::default(), &[&term], &[], &mut |_| false));
}

#[test]
fn source_owner_and_merged_function_signature_conflicts_refuse() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let mut sigs = tables.sigs.clone();
    sigs.get_mut(&FnId(DefHash::new(57, 1))).unwrap().owner = FnId(DefHash::new(57, 99));
    assert!(Vocabulary::new(&ctx, &tables.functions, &sigs, &mut |_| true).is_none());
    let mut functions = tables.functions.clone();
    let mut other = functions.iter().find(|f| f.name == "sf0").unwrap().clone();
    other.ret = Sort::Int;
    functions.push(other);
    assert!(Vocabulary::new(&ctx, &functions, &tables.sigs, &mut |_| true).is_none());
}

#[test]
fn parameter_environments_do_not_register_closed_type_permissions() {
    use super::super::type_encoding::{TypeRecipe, Vocabulary as Encoding};
    let owner = FnId(DefHash::new(57, 9));
    let argument = TypeArgument::new(
        Term::call("closed_looking_dec", vec![], Sort::Decoration),
        Term::call("closed_looking_type", vec![], Sort::TypeId),
    )
    .unwrap();
    let mut encoding = Encoding::default();
    let env = TypeEnv::new(owner, vec![argument.clone()]);
    let recipe = TypeRecipe::Parameter { owner, index: 0 };
    assert_eq!(encoding.argument(&recipe, &env), Some(argument));
    assert!(encoding.closed_arguments().is_empty());
    assert!(encoding
        .argument(&TypeRecipe::SharedRef(Box::new(recipe)), &env)
        .is_some());
    assert!(
        encoding.closed_arguments().is_empty(),
        "a partly symbolic recipe is not a closed license"
    );
}

#[test]
fn malformed_operator_and_hidden_variable_sorts_refuse() {
    use super::super::term::ArithOp;
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let malformed = [
        Term::Arith(
            ArithOp::Add,
            Box::new(Term::Bool(true)),
            Box::new(Term::Int(1)),
        ),
        Term::Ite(
            Box::new(Term::Bool(true)),
            Box::new(Term::Int(1)),
            Box::new(Term::Int(2)),
            Sort::Poly,
        ),
        Term::Var {
            name: "unbound_box".into(),
            sort: Sort::Poly,
        },
        Term::Var {
            name: "undeclared_carrier".into(),
            sort: Sort::Nominal(999),
        },
    ];
    for term in malformed {
        assert!(!vocabulary.ground(&registry, &term, &mut |_| true));
    }
}

#[test]
fn negative_native_int_never_gets_unconditional_nat_membership() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::Int(-3));
    let Term::Call { args, .. } = &term else {
        panic!("typed generic call");
    };
    let member = Term::call(
        "has_type",
        vec![args[2].clone(), args[1].clone()],
        Sort::Bool,
    );
    let facts = ctx.bridge_axioms(&[&term, &member], &mut 100_000).unwrap();
    assert!(!facts.contains(&member));
    assert!(
        !facts.contains(&Term::Bool(false)),
        "an out-of-domain application is not a contradiction or a witness"
    );
    let guarded = facts
        .iter()
        .filter(|fact| matches!(fact, Term::Implies(_, _)))
        .count();
    assert!(
        guarded > 0,
        "membership-dependent reconstruction/range laws remain conditional"
    );
}

#[test]
fn unfunded_snapshot_and_signature_copy_refuse_before_allocation() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    assert!(Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| false).is_none());
    let wide = Function {
        name: "wide".into(),
        params: vec![Sort::Int; 10_000],
        ret: Sort::Bool,
    };
    let mut left = 16usize;
    let mut denied = Vec::new();
    let mut pay = |cost| match left.checked_sub(cost) {
        Some(next) => {
            left = next;
            true
        }
        None => {
            denied.push(cost);
            false
        }
    };
    assert!(Vocabulary::new(&ctx, &[wide], &HashMap::new(), &mut pay).is_none());
    assert_eq!(denied.len(), 1);
    assert!(
        denied[0] > 10_000,
        "the entire signature copy is admitted before copying its vector"
    );
}

#[test]
fn snapshot_and_term_check_share_one_ledger_without_a_live_encoding_borrow() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::var("x", Sort::Int));
    let mut snapshot_cost = 0usize;
    let measured = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |cost| {
        snapshot_cost = snapshot_cost.checked_add(cost).unwrap();
        true
    })
    .unwrap();
    assert!(snapshot_cost > 0);
    let mut left = snapshot_cost;
    let mut pay = |cost| match left.checked_sub(cost) {
        Some(next) => {
            left = next;
            true
        }
        None => false,
    };
    let exact = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut pay).unwrap();
    assert!(
        !exact.check(&Registry::default(), &[&term], &[], &mut pay),
        "capture cannot refill the checker budget"
    );
    assert_eq!(left, 0);
    // The snapshot owns its data. Bridge generation takes the real mutable
    // encoding borrow while BOTH snapshots are alive; no ambient Ref survives.
    assert!(ctx.bridge_axioms(&[&term], &mut 100_000).is_some());
    assert!(measured.check(&Registry::default(), &[&term], &[], &mut |_| true));
}

#[test]
fn registered_signature_lookup_borrows_and_argument_scan_is_admitted() {
    let source = source();
    let ctx = Ctx::new(&source);
    let wide = Function {
        name: "wide".into(),
        params: vec![Sort::Int; 10_000],
        ret: Sort::Bool,
    };
    let vocabulary = Vocabulary::new(&ctx, &[wide], &HashMap::new(), &mut |_| true).unwrap();
    let registry = Registry::default();
    let (params, ret) = vocabulary
        .signature(&registry, "wide", &mut |_| true)
        .unwrap();
    assert_eq!(ret, Sort::Bool);
    assert!(
        std::ptr::eq(
            params.as_ptr(),
            vocabulary.functions["wide"].params.as_ptr()
        ),
        "lookup returns the owned slice, not a cloned signature"
    );
    let arguments = vec![Term::Int(0); 10_000];
    let mut left = 64usize;
    let mut denied = Vec::new();
    let mut pay = |cost| match left.checked_sub(cost) {
        Some(next) => {
            left = next;
            true
        }
        None => {
            denied.push(cost);
            false
        }
    };
    assert!(!vocabulary.call_is_typed(&registry, "wide", &arguments, Sort::Bool, &mut pay));
    assert_eq!(denied.len(), 1);
    assert!(denied[0] >= 10_000);
    assert!(vocabulary.call_is_typed(&registry, "wide", &arguments, Sort::Bool, &mut |_| true));
}

#[test]
fn closed_pair_byte_comparison_and_subtree_census_pay_before_copy_or_lookup() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let term = application(&ctx, &tables, Ty::nat(), Term::Int(3));
    let Term::Call { name, mut args, .. } = term else {
        panic!("actual source generic application");
    };
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    args[0] = Term::call(
        "unregistered_decoration".repeat(4096),
        vec![],
        Sort::Decoration,
    );
    let mut denied = false;
    let mut pay = |cost| {
        if cost > 256 {
            denied = true;
            false
        } else {
            true
        }
    };
    assert!(!vocabulary.call_is_typed(&Registry::default(), &name, &args, Sort::Bool, &mut pay));
    assert!(
        denied,
        "the borrowed type name is charged before structural comparison"
    );
    let mut calls = 0usize;
    let named_tree = Term::call(
        "unregistered_decoration".repeat(4096),
        vec![Term::var("unvisited_tail", Sort::Int)],
        Sort::Decoration,
    );
    assert!(!charge_term(&named_tree, &mut |cost| {
        calls += 1;
        cost <= 256
    }));
    assert_eq!(
        calls, 2,
        "census stops on the unpaid name without reading its children"
    );
}
