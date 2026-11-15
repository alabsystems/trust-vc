//! Sort, binder and ground boxing controls.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::DefHash;

fn environment(owner: u64, prefix: &str) -> TypeEnv {
    TypeEnv::new(
        FnId(DefHash::new(1, owner)),
        vec![TypeArgument::named(
            format!("{prefix}d"),
            format!("{prefix}t"),
        )],
    )
}

fn parameter(owner: u64, index: u32) -> TypeRecipe {
    TypeRecipe::Parameter {
        owner: FnId(DefHash::new(1, owner)),
        index,
    }
}

#[test]
fn type_arguments_reject_crossed_sorts() {
    let decoration = Term::var("d", Sort::Decoration);
    let identity = Term::var("t", Sort::TypeId);
    assert!(TypeArgument::new(decoration.clone(), identity.clone()).is_some());
    assert!(TypeArgument::new(identity, decoration).is_none());
    assert!(TypeArgument::new(Term::Int(0), Term::Int(1)).is_none());
}

#[test]
fn equal_parameter_numbers_do_not_supply_another_binders_identity() {
    let mut vocabulary = Vocabulary::default();
    let recipe = parameter(1, 0);
    let first = environment(1, "a");
    let second = environment(2, "b");
    assert_ne!(first.owner(), second.owner());
    assert_ne!(
        vocabulary.argument(&recipe, &first),
        vocabulary.argument(&parameter(2, 0), &second)
    );
    assert_eq!(vocabulary.argument(&recipe, &second), None);
    assert_ne!(
        vocabulary.intern(recipe.clone()),
        vocabulary.intern(parameter(2, 0))
    );
    assert_eq!(vocabulary.argument(&recipe, &TypeEnv::default()), None);
    assert_eq!(vocabulary.argument(&parameter(1, 1), &first), None);
}

#[test]
fn opaque_recipes_require_registered_identity_and_exact_arity() {
    let first = AdtId(DefHash::new(2, 1));
    let second = AdtId(DefHash::new(2, 2));
    let arity = |id| (id == first).then_some(RecipeAdt::Opaque(1));
    let admitted = Ty::Adt(first, vec![Ty::Param(0)]);
    assert!(TypeRecipe::registered(&admitted, Some(FnId(DefHash::new(1, 1))), &arity).is_some());
    assert!(TypeRecipe::registered(&admitted, None, &arity).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Adt(second, vec![Ty::Param(0)]),
        Some(FnId(DefHash::new(1, 1))),
        &arity
    )
    .is_none());
    assert!(TypeRecipe::registered(&Ty::Adt(first, vec![]), None, &arity).is_none());
    assert!(
        TypeRecipe::registered(&Ty::Adt(first, vec![Ty::Bool, Ty::Bool]), None, &arity).is_none()
    );
}

#[test]
fn nested_type_recipes_have_a_fixed_work_bound() {
    let mut ty = Ty::Bool;
    for _ in 0..65 {
        ty = Ty::Ref {
            mutable: false,
            inner: Box::new(ty),
        };
    }
    assert!(TypeRecipe::registered(&ty, None, &|_| None).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Ref {
            mutable: true,
            inner: Box::new(Ty::Bool)
        },
        None,
        &|_| None
    )
    .is_none());
}

#[test]
fn decorations_are_retained_when_underlying_identity_is_shared() {
    let mut vocabulary = Vocabulary::default();
    let env = TypeEnv::default();
    let plain = vocabulary.argument(&TypeRecipe::Bool, &env).unwrap();
    let borrowed = vocabulary
        .argument(&TypeRecipe::SharedRef(Box::new(TypeRecipe::Bool)), &env)
        .unwrap();
    assert_eq!(plain.identity(), borrowed.identity());
    assert_ne!(plain.terms(), borrowed.terms());
}

#[test]
fn opaque_type_constructors_retain_arguments_and_declaration_identity() {
    let mut vocabulary = Vocabulary::default();
    let first = AdtId(DefHash::new(2, 1));
    let second = AdtId(DefHash::new(2, 2));
    let recipe = TypeRecipe::Opaque(first, vec![parameter(1, 0)]);
    let a = vocabulary.argument(&recipe, &environment(1, "a")).unwrap();
    let b = vocabulary
        .argument(
            &TypeRecipe::Opaque(first, vec![parameter(2, 0)]),
            &environment(2, "b"),
        )
        .unwrap();
    let other = vocabulary
        .argument(
            &TypeRecipe::Opaque(second, vec![parameter(1, 0)]),
            &environment(1, "a"),
        )
        .unwrap();
    assert_ne!(a.identity(), b.identity());
    assert_ne!(a.identity(), other.identity());
}

#[test]
fn membership_requires_a_poly_value_and_type_identity() {
    let mut vocabulary = Vocabulary::default();
    let p = Term::var("p", Sort::Poly);
    let t = Term::var("t", Sort::TypeId);
    assert!(vocabulary.membership(p.clone(), t.clone()).is_some());
    assert!(vocabulary.membership(Term::Int(0), t).is_none());
    assert!(vocabulary
        .membership(p, Term::var("d", Sort::Decoration))
        .is_none());
}

#[test]
fn unboxing_a_native_box_preserves_its_value() {
    let mut vocabulary = Vocabulary::default();
    let identity = vocabulary
        .argument(&TypeRecipe::Int(IntRange::Int), &TypeEnv::default())
        .unwrap();
    let x = Term::var("x", Sort::Int);
    let boxed = vocabulary
        .box_value(
            Sort::Int,
            identity.identity.clone(),
            (None, None),
            x.clone(),
        )
        .unwrap();
    assert_eq!(
        vocabulary.unbox_value(Sort::Int, identity.identity, (None, None), boxed),
        Some(x)
    );
}

#[test]
fn native_sort_conflicts_do_not_change_an_existing_bridge() {
    let mut vocabulary = Vocabulary::default();
    let identity = Term::var("type", Sort::TypeId);
    let p = vocabulary
        .box_value(Sort::Int, identity.clone(), (None, None), Term::Int(0))
        .unwrap();
    assert!(vocabulary
        .box_value(Sort::Bool, identity.clone(), (None, None), Term::Bool(true))
        .is_none());
    assert_eq!(
        vocabulary.unbox_value(Sort::Int, identity, (None, None), p),
        Some(Term::Int(0))
    );
}

#[test]
fn an_untyped_poly_value_does_not_receive_a_nat_bound() {
    let mut vocabulary = Vocabulary::default();
    let identity = vocabulary
        .argument(&TypeRecipe::Int(IntRange::Nat), &TypeEnv::default())
        .unwrap();
    let p = Term::var("p", Sort::Poly);
    let n = vocabulary
        .unbox_value(
            Sort::Int,
            identity.identity.clone(),
            (Some(0), None),
            p.clone(),
        )
        .unwrap();
    assert!(vocabulary
        .bridge_axioms(&[&n], &mut 10_000)
        .unwrap()
        .is_empty());
    let membership = vocabulary.membership(p, identity.identity).unwrap();
    let facts = vocabulary
        .bridge_axioms(&[&n, &membership], &mut 10_000)
        .unwrap();
    assert!(facts.contains(&Term::implies(membership, n.within(Some(0), None))));
    assert!(!facts.contains(&n.within(Some(0), None)));
}

#[test]
fn boxed_nat_membership_keeps_its_native_range_guard() {
    let mut vocabulary = Vocabulary::default();
    let identity = vocabulary
        .argument(&TypeRecipe::Int(IntRange::Nat), &TypeEnv::default())
        .unwrap();
    let x = Term::var("x", Sort::Int);
    let boxed = vocabulary
        .box_value(
            Sort::Int,
            identity.identity.clone(),
            (Some(0), None),
            x.clone(),
        )
        .unwrap();
    let membership = vocabulary
        .membership(boxed.clone(), identity.identity)
        .unwrap();
    let facts = vocabulary
        .bridge_axioms(&[&boxed, &membership], &mut 10_000)
        .unwrap();
    assert!(facts.contains(&Term::implies(x.within(Some(0), None), membership)));
    assert!(vocabulary
        .functions()
        .iter()
        .all(|function| function.name != "as_type"));
    assert!(vocabulary.bridge_axioms(&[&boxed], &mut 0).is_none());
}
