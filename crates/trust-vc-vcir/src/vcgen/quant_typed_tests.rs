// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::closed_templates::{
    tests::{application, source},
    Vocabulary,
};
use super::super::spec::Tables;
use super::super::val::Ctx;
use super::*;
use crate::Ty;

#[test]
fn trigger_matching_keeps_complete_rigid_type_and_decoration_vectors() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let pattern = application(&ctx, &tables, Ty::nat(), Term::var("qx0", Sort::Int));
    let same = application(&ctx, &tables, Ty::nat(), Term::Int(5));
    let integer = application(&ctx, &tables, Ty::int(), Term::Int(5));
    let reference = application(
        &ctx,
        &tables,
        Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::nat()),
        },
        Term::Int(5),
    );
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let mut binding = HashMap::new();
    assert!(matches(
        &pattern,
        &same,
        &mut binding,
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    ));
    assert_eq!(binding.get("qx0"), Some(&Term::Int(5)));
    for other in [integer, reference] {
        assert!(!matches(
            &pattern,
            &other,
            &mut HashMap::new(),
            &[Sort::Int],
            &vocabulary,
            &registry,
            &mut |_| true
        ));
    }
}

#[test]
fn canonical_binders_substitution_lengths_and_sorts_are_checked() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    for name in ["qx00", "qx1", "qxgarbage"] {
        assert!(!matches(
            &Term::var(name, Sort::Int),
            &Term::Int(2),
            &mut HashMap::new(),
            &[Sort::Int],
            &vocabulary,
            &registry,
            &mut |_| true
        ));
    }
    let bound = Term::var("qx0", Sort::Int);
    assert!(at(&bound, &[], &[Term::Bool(true)], &[], &[Sort::Int]).is_none());
    assert!(at(&bound, &[], &[], &[], &[Sort::Int]).is_none());
    assert!(at(&bound, &[], &[Term::Int(2)], &[], &[Sort::Int]).is_some());
    let parameter = Term::var("qp0", Sort::Bool);
    assert!(with_params(&[parameter], &[Term::Int(2)], &[Sort::Bool], &[]).is_none());
    assert!(!matches(
        &bound,
        &Term::Bool(true),
        &mut HashMap::new(),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    ));
    assert!(atom_of("qa00").is_none());
    assert!(choose_of("ch00_0").is_none());
    assert!(choose_of("ch0_00").is_none());
    let mut atoms = Registry::default();
    let atom = atoms
        .quant(
            QuantKind::Forall,
            &[("x".into(), Sort::Int)],
            Term::var("p", Sort::Bool),
            vec![],
        )
        .unwrap();
    let Term::Call { name, args, .. } = atom else {
        panic!("actual registered QA");
    };
    assert!(vocabulary.call_is_typed(&atoms, &name, &args, Sort::Bool, &mut |_| true));
    assert!(!vocabulary.call_is_typed(&atoms, &name, &args, Sort::Int, &mut |_| true));
    assert!(!vocabulary.call_is_typed(&atoms, &name, &[Term::Int(1)], Sort::Bool, &mut |_| true));
    assert!(!vocabulary.call_is_typed(&atoms, &name, &[], Sort::Bool, &mut |_| true));
}

#[test]
fn repeated_variables_and_malformed_registered_return_sorts_refuse() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let pattern = application(&ctx, &tables, Ty::nat(), Term::var("qx0", Sort::Int));
    let Term::Call { name, args, .. } = &pattern else {
        panic!("SF call");
    };
    let malformed = Term::call(name, args.clone(), Sort::Int);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let mut registry = Registry::default();
    assert!(!matches(
        &pattern,
        &malformed,
        &mut HashMap::new(),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    ));
    let same_name = Term::and([
        Term::var("x", Sort::Bool),
        Term::eq(Term::var("x", Sort::Int), Term::Int(0)),
    ]);
    assert!(registry
        .quant(QuantKind::Forall, &[], same_name, vec![])
        .is_none());
    assert!(registry
        .quant(
            QuantKind::Forall,
            &[("x".into(), Sort::Int)],
            Term::var("x", Sort::Bool),
            vec![]
        )
        .is_none());
    assert!(registry
        .quant(QuantKind::Forall, &[], Term::Int(1), vec![])
        .is_none());
}

#[test]
fn a_negative_int_trigger_keeps_the_nat_domain_inside_the_instance() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let x = Term::var("qx0", Sort::Int);
    let predicate = application(&ctx, &tables, Ty::nat(), x.clone());
    let domain = x.within(Some(0), None);
    let body = Term::and([domain, predicate]);
    let instance = at(&body, &[], &[Term::Int(-3)], &[], &[Sort::Int]).unwrap();
    assert_eq!(instance, Term::Bool(false));
    let literal = Term::call("sf1", vec![Term::Int(-3)], Sort::Bool);
    let trigger = Term::call("sf1", vec![x], Sort::Bool);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let item = (literal, Term::Bool(true));
    let index = [("sf1", vec![&item])].into_iter().collect();
    let found = bindings(
        &[trigger],
        &index,
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true,
    );
    assert_eq!(found.len(), 1);
    assert_eq!(
        at(&body, &[], &found[0].0, &[], &[Sort::Int]),
        Some(Term::Bool(false))
    );
}

#[test]
fn whole_binding_vector_and_recursive_work_are_bounded() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let items: Vec<Item> = (0..250)
        .map(|n| {
            (
                Term::call("sf1", vec![Term::Int(n)], Sort::Bool),
                Term::Bool(true),
            )
        })
        .collect();
    let index = [("sf1", items.iter().collect())].into_iter().collect();
    let patterns = [
        Term::call("sf1", vec![Term::var("qx0", Sort::Int)], Sort::Bool),
        Term::call("sf1", vec![Term::var("qx1", Sort::Int)], Sort::Bool),
    ];
    let found = bindings(
        &patterns,
        &index,
        &[Sort::Int, Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true,
    );
    assert_eq!(found.len(), MAX_BINDINGS);
    assert!(bindings(
        &patterns,
        &index,
        &[Sort::Int, Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| false
    )
    .is_empty());
}

#[test]
fn substitution_census_stops_at_unpaid_replacement_names_without_a_size_walk() {
    let template = Term::var("qx0", Sort::Int);
    let replacement = Term::var("long_native_value".repeat(4096), Sort::Int);
    let mut denied = Vec::new();
    let mut pay = |cost| {
        if cost <= 256 {
            true
        } else {
            denied.push(cost);
            false
        }
    };
    assert!(!charge_substitution(
        &template,
        &[],
        &[replacement.clone()],
        &mut pay
    ));
    assert_eq!(denied.len(), 1);
    assert!(denied[0] > 256);
    assert_eq!(
        at(&template, &[], &[replacement.clone()], &[], &[Sort::Int]),
        Some(replacement)
    );
}
