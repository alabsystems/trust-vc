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

fn projection(number: u64, arguments: Vec<Ty>, owner: Option<FnId>) -> Option<TypeRecipe> {
    let id = ProjectionId(DefHash::new(710, number));
    TypeRecipe::registered(
        &Ty::Projection(id, arguments), owner, &|_| None,
        &|candidate| (candidate == id).then_some(1),
    )
}

#[test]
fn associated_constructors_require_declared_identity_arity_and_binder_scope() {
    let owner = FnId(DefHash::new(1, 1));
    assert!(projection(1, vec![Ty::Param(0)], Some(owner)).is_some());
    assert!(projection(1, vec![Ty::Param(0)], None).is_none());
    assert!(projection(1, vec![], Some(owner)).is_none());
    assert!(projection(1, vec![Ty::Bool, Ty::Bool], Some(owner)).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Projection(ProjectionId(DefHash::new(710, 2)), vec![Ty::Bool]),
        Some(owner), &|_| None, &|_| None,
    ).is_none());
    let mut vocabulary = Vocabulary::default();
    let recipe = projection(1, vec![Ty::Param(0)], Some(owner)).unwrap();
    let work = std::cell::Cell::new(1_000);
    assert!(vocabulary.argument_with_work(&recipe, &environment(2, "other"), &work, crate::SpanId(0)).unwrap().is_none());
}

#[test]
fn associated_type_arguments_keep_two_sorts_and_each_actual_declaration_and_argument() {
    let owner = Some(FnId(DefHash::new(1, 1)));
    let mut vocabulary = Vocabulary::default();
    let work = std::cell::Cell::new(10_000);
    let first = projection(1, vec![Ty::Param(0)], owner).unwrap();
    let second = projection(2, vec![Ty::Param(0)], owner).unwrap();
    let a = vocabulary.argument_with_work(&first, &environment(1, "a"), &work, crate::SpanId(0)).unwrap().unwrap();
    let repeated = vocabulary.argument_with_work(&first, &environment(1, "a"), &work, crate::SpanId(0)).unwrap().unwrap();
    let other_self = vocabulary.argument_with_work(&first, &environment(1, "b"), &work, crate::SpanId(0)).unwrap().unwrap();
    let other_declaration = vocabulary.argument_with_work(&second, &environment(1, "a"), &work, crate::SpanId(0)).unwrap().unwrap();
    assert_eq!(a, repeated);
    assert_ne!(a, other_self);
    assert_ne!(a, other_declaration);
    assert_eq!(a.decoration.sort(), Sort::Decoration);
    assert_eq!(a.identity.sort(), Sort::TypeId);
    // Type constructors declare no equality, value membership or ownership
    // axiom. They are simply distinct typed applications in this vocabulary.
    assert!(vocabulary.closed_arguments().is_empty());
}

#[test]
fn projected_terms_and_forwarded_arguments_spend_the_same_caller_work_cell() {
    let owner = FnId(DefHash::new(1, 1));
    let recipe = projection(1, vec![Ty::Param(0)], Some(owner)).unwrap();
    let mut vocabulary = Vocabulary::default();
    let env = environment(1, "a");
    assert!(vocabulary.argument(&recipe, &env).is_none());
    let work = std::cell::Cell::new(10_000);
    let before = work.get();
    let argument = vocabulary.argument_with_work(&recipe, &env, &work, crate::SpanId(0)).unwrap().unwrap();
    assert!(work.get() < before);
    let forwarded = TypeEnv::new(owner, vec![argument]);
    assert!(vocabulary.argument(&parameter(1, 0), &forwarded).is_none());
    let available = work.get();
    let _ = vocabulary.argument_with_work(&parameter(1, 0), &forwarded, &work, crate::SpanId(0)).unwrap().unwrap();
    assert!(work.get() < available);
    // Exhaust the very same cell. No re-created translator or vocabulary may
    // convert a failed debit into an unmetered projected type argument.
    work.set(0);
    assert!(vocabulary.argument_with_work(&parameter(1, 0), &forwarded, &work, crate::SpanId(0)).is_err());
    assert_eq!(work.get(), 0);
    assert!(vocabulary.closed_arguments().is_empty());
}

#[test]
fn repeated_projection_terms_cannot_expand_past_the_existing_work_budget() {
    let mut ty = Ty::Param(0);
    let id = ProjectionId(DefHash::new(710, 1));
    for _ in 0..20 { ty = Ty::Projection(id, vec![ty]); }
    let recipe = TypeRecipe::registered(
        &ty, Some(FnId(DefHash::new(1, 1))), &|_| None, &|candidate| (candidate == id).then_some(1),
    ).unwrap();
    let mut vocabulary = Vocabulary::default();
    let work = std::cell::Cell::new(10_000);
    assert!(vocabulary.argument_with_work(&recipe, &environment(1, "a"), &work, crate::SpanId(0)).is_err());
    let remaining = work.get();
    assert!(vocabulary.argument_with_work(&recipe, &environment(1, "a"), &work, crate::SpanId(0)).is_err());
    assert!(work.get() <= remaining);
    assert!(vocabulary.closed_arguments().is_empty());
}

#[test]
fn projected_environments_share_immutable_arguments_and_cannot_replace_their_ledger() {
    let owner = FnId(DefHash::new(1, 1));
    let mut vocabulary = Vocabulary::default();
    let work = std::rc::Rc::new(std::cell::Cell::new(10_000));
    let recipe = projection(1, vec![Ty::Param(0)], Some(owner)).unwrap();
    let argument = vocabulary.argument_with_work(&recipe, &environment(1, "a"), &work, crate::SpanId(0)).unwrap().unwrap();
    let env = vocabulary.environment(owner, vec![argument], &work);
    let copied = env.clone();
    assert!(std::rc::Rc::ptr_eq(&env.arguments, &copied.arguments));
    assert!(std::rc::Rc::ptr_eq(env.projection_work().unwrap(), &work));
    assert!(std::rc::Rc::ptr_eq(copied.projection_work().unwrap(), &work));
    work.set(0);
    let substitute = std::cell::Cell::new(10_000);
    assert!(vocabulary.argument_with_work(&parameter(1, 0), &copied, &substitute, crate::SpanId(0)).is_err());
    assert_eq!(substitute.get(), 10_000);
    assert_eq!(work.get(), 0);
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
    assert!(TypeRecipe::registered(&admitted, Some(FnId(DefHash::new(1, 1))), &arity,
            &|_| None).is_some());
    assert!(TypeRecipe::registered(&admitted, None, &arity,
            &|_| None).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Adt(second, vec![Ty::Param(0)]),
        Some(FnId(DefHash::new(1, 1))),
        &arity
    ,
            &|_| None)
    .is_none());
    assert!(TypeRecipe::registered(&Ty::Adt(first, vec![]), None, &arity,
            &|_| None).is_none());
    assert!(
        TypeRecipe::registered(&Ty::Adt(first, vec![Ty::Bool, Ty::Bool]), None, &arity,
            &|_| None).is_none()
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
    assert!(TypeRecipe::registered(&ty, None, &|_| None,
            &|_| None).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Ref {
            mutable: true,
            inner: Box::new(Ty::Bool)
        },
        None,
        &|_| None
    ,
            &|_| None)
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

#[test]
fn closed_projection_terms_reduce_both_sorts_only_at_the_exact_domain() {
    let mut vocabulary = Vocabulary::default();
    let id = ProjectionId(crate::DefHash::new(400, 1));
    let other = ProjectionId(crate::DefHash::new(400, 2));
    let env = TypeEnv::default();
    let input = vocabulary.argument(&TypeRecipe::Bool, &env).unwrap();
    let output = vocabulary.argument(&TypeRecipe::Int(IntRange::U(16)), &env).unwrap();
    let work = std::cell::Cell::new(100_000);
    vocabulary.register_projection_definition(id, &[input], &output, &work, crate::SpanId(0)).unwrap();
    let raw = vocabulary.argument_with_work(&TypeRecipe::Projection(id, vec![TypeRecipe::Bool]), &env, &work, crate::SpanId(0)).unwrap().unwrap();
    assert_ne!(raw, output);
    let mut remaining = 100_000;
    assert_eq!(vocabulary.canonical_argument(raw.clone(), &mut remaining), Some(output));
    let cost = 100_000 - remaining;
    let mut one_short = cost - 1;
    assert!(vocabulary.canonical_argument(raw, &mut one_short).is_none());
    let wrong_domain = vocabulary.argument_with_work(&TypeRecipe::Projection(id, vec![TypeRecipe::Int(IntRange::U(8))]), &env, &work, crate::SpanId(0)).unwrap().unwrap();
    let wrong_member = vocabulary.argument_with_work(&TypeRecipe::Projection(other, vec![TypeRecipe::Bool]), &env, &work, crate::SpanId(0)).unwrap().unwrap();
    assert_eq!(vocabulary.canonical_argument(wrong_domain.clone(), &mut 100_000), Some(wrong_domain));
    assert_eq!(vocabulary.canonical_argument(wrong_member.clone(), &mut 100_000), Some(wrong_member));
    // Reductions interpret private constructors. They add no equality axiom
    // or blanket membership for arbitrary values.
    assert!(vocabulary.bridge_axioms(&[], &mut 100_000).unwrap().is_empty());
}
