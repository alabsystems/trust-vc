// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed family, substitution and guarded ground-law controls.

use super::super::RecipeAdt;
use super::*;
use crate::{AdtId, DefHash, FnId, IntRange, Ty};

fn family(index: u64) -> ProductFamily {
    ProductFamily::Struct(AdtId(DefHash::new(41, index)))
}
fn parameter(owner: ProductFamily, index: u32) -> TypeRecipe {
    TypeRecipe::ProductParameter { owner, index }
}
fn p(name: &str) -> Term {
    Term::var(name, Sort::Poly)
}
fn argument(vocabulary: &mut Vocabulary, recipe: TypeRecipe) -> TypeArgument {
    vocabulary.argument(&recipe, &TypeEnv::default()).unwrap()
}
fn register(vocabulary: &mut Vocabulary, family: ProductFamily) {
    assert!(vocabulary
        .register_product(family, 1, vec![parameter(family, 0), TypeRecipe::Bool])
        .is_some());
}

#[test]
fn associated_product_fields_require_the_registered_member_and_original_work() {
    let mut vocabulary = Vocabulary::default();
    let owner = family(91);
    let member = crate::ProjectionId(DefHash::new(400, 91));
    let recipe = TypeRecipe::Projection(member, vec![parameter(owner, 0)]);
    let work = std::cell::Cell::new(100_000);
    assert!(vocabulary.register_product(owner, 1, vec![recipe.clone()]).is_none());
    assert!(vocabulary.register_product_with_work(owner, 1, vec![recipe.clone()], &work, crate::SpanId(0)).unwrap().is_none());
    vocabulary.register_projection_declaration(member, 1).unwrap();
    assert!(vocabulary.register_product_with_work(owner, 1, vec![recipe], &work, crate::SpanId(0)).unwrap().is_some());
    let actual = argument(&mut vocabulary, TypeRecipe::Bool);
    assert!(vocabulary.pack_product(owner, &[actual.clone()], vec![p("value")]).is_none());
    let value = vocabulary.pack_product_with_work(owner, &[actual.clone()], vec![p("value")], &work, crate::SpanId(0)).unwrap().unwrap();
    assert!(vocabulary.project_product(owner, &[actual.clone()], value.clone()).is_none());
    assert_eq!(vocabulary.project_product_with_work(owner, &[actual.clone()], value.clone(), &work, crate::SpanId(0)).unwrap().unwrap().len(), 1);
    work.set(0);
    assert!(vocabulary.project_product_with_work(owner, &[actual], value, &work, crate::SpanId(0)).is_err());
    assert_eq!(work.get(), 0);
}

#[test]
fn associated_product_laws_keep_membership_guards_and_query_exhaustion() {
    let mut vocabulary = Vocabulary::default();
    let owner = family(92);
    let member = crate::ProjectionId(DefHash::new(400, 92));
    vocabulary.register_projection_declaration(member, 1).unwrap();
    let work = std::cell::Cell::new(100_000);
    vocabulary.register_product_with_work(owner, 1,
        vec![TypeRecipe::Projection(member, vec![parameter(owner, 0)])], &work, crate::SpanId(0)).unwrap().unwrap();
    let ty = argument(&mut vocabulary, TypeRecipe::Bool);
    let packed = vocabulary.pack_product_with_work(owner, &[ty], vec![p("x")], &work, crate::SpanId(0)).unwrap().unwrap();
    let mut query_work = 100_000;
    let facts = vocabulary.bridge_axioms(&[&packed], &mut query_work).unwrap();
    assert!(!facts.is_empty());
    assert!(facts.iter().any(|fact| matches!(fact, Term::Implies(_, _))));
    assert!(!facts.contains(&Term::Bool(false)));
    let mut exhausted = 0;
    assert!(vocabulary.bridge_axioms(&[&packed], &mut exhausted).is_none());
    assert_eq!(exhausted, 0);
}

#[test]
fn unary_tuple_product_keeps_unit_and_nested_type_identities_distinct() {
    let mut vocabulary = Vocabulary::default();
    let family = ProductFamily::Tuple(1);
    assert!(vocabulary
        .register_product(ProductFamily::Unit, 0, vec![])
        .is_some());
    assert!(vocabulary
        .register_product(family, 1, vec![parameter(family, 0)])
        .is_some());
    let unit_type = argument(&mut vocabulary, TypeRecipe::Unit);
    let tuple_type = argument(&mut vocabulary, TypeRecipe::Tuple(vec![TypeRecipe::Unit]));
    let nested_type = argument(
        &mut vocabulary,
        TypeRecipe::Tuple(vec![TypeRecipe::Tuple(vec![TypeRecipe::Unit])]),
    );
    assert_ne!(unit_type.identity(), tuple_type.identity());
    assert_ne!(tuple_type.identity(), nested_type.identity());
    let unit = vocabulary
        .pack_product(ProductFamily::Unit, &[], vec![])
        .unwrap();
    let tuple = vocabulary
        .pack_product(family, std::slice::from_ref(&unit_type), vec![unit.clone()])
        .unwrap();
    assert_ne!(unit, tuple);
    assert_eq!(
        vocabulary
            .project_product(family, std::slice::from_ref(&unit_type), tuple.clone())
            .unwrap()
            .len(),
        1
    );
    assert!(vocabulary
        .project_product(family, &[], tuple.clone())
        .is_none());
    assert!(vocabulary
        .pack_product(family, std::slice::from_ref(&unit_type), vec![])
        .is_none());
    assert!(vocabulary
        .pack_product(ProductFamily::Unit, &[unit_type], vec![tuple])
        .is_none());
    assert!(vocabulary
        .register_product(ProductFamily::Tuple(0), 0, vec![])
        .is_none());
    assert!(TypeRecipe::registered(&Ty::Tuple(vec![]), None, &|_| None,
            &|_| None).is_none());
}

#[test]
fn product_recipes_require_registered_nominals_and_exact_arity() {
    let ProductFamily::Struct(id) = family(1) else {
        unreachable!()
    };
    let registered = |actual| (actual == id).then_some(RecipeAdt::Struct(1));
    let ty = Ty::Adt(id, vec![Ty::Int(IntRange::Int)]);
    assert!(
        matches!(TypeRecipe::registered(&ty, None, &registered,
            &|_| None), Some(TypeRecipe::Struct(actual, _)) if actual == id)
    );
    assert!(TypeRecipe::registered(&Ty::Adt(id, vec![]), None, &registered,
            &|_| None).is_none());
    assert!(TypeRecipe::registered(&ty, None, &|_| None,
            &|_| None).is_none());
    assert!(TypeRecipe::registered(&Ty::Adt(id, vec![Ty::Param(0)]), None, &registered,
            &|_| None).is_none());
    assert!(TypeRecipe::registered(
        &Ty::Ref {
            mutable: true,
            inner: Box::new(ty)
        },
        None,
        &registered
    ,
            &|_| None)
    .is_none());
}

#[test]
fn product_schema_parameters_have_a_distinct_checked_owner() {
    let mut vocabulary = Vocabulary::default();
    let a = family(1);
    assert!(vocabulary
        .register_product(a, 1, vec![parameter(family(2), 0)])
        .is_none());
    assert!(vocabulary
        .register_product(a, 1, vec![parameter(a, 1)])
        .is_none());
    assert!(vocabulary
        .register_product(
            a,
            1,
            vec![TypeRecipe::Parameter {
                owner: FnId(DefHash::new(41, 1)),
                index: 0
            }]
        )
        .is_none());
    register(&mut vocabulary, a);
    assert!(vocabulary
        .register_product(a, 1, vec![TypeRecipe::Bool, parameter(a, 0)])
        .is_none());
    assert!(vocabulary
        .register_product(a, 0, vec![TypeRecipe::Bool])
        .is_none());
    assert!(vocabulary
        .argument(
            &parameter(a, 0),
            &TypeEnv::new(
                FnId(DefHash::new(41, 1)),
                vec![TypeArgument::named("d".into(), "t".into())]
            )
        )
        .is_none());
    assert!(vocabulary
        .register_product(
            ProductFamily::Tuple(2),
            1,
            vec![parameter(ProductFamily::Tuple(2), 0)]
        )
        .is_none());
}

#[test]
fn opaque_registration_never_becomes_a_transparent_product() {
    let mut vocabulary = Vocabulary::default();
    let ProductFamily::Struct(id) = family(1) else {
        unreachable!()
    };
    argument(
        &mut vocabulary,
        TypeRecipe::Opaque(id, vec![TypeRecipe::Bool]),
    );
    assert!(vocabulary
        .register_product(family(1), 1, vec![parameter(family(1), 0)])
        .is_none());
    assert!(vocabulary
        .argument(
            &TypeRecipe::Struct(id, vec![TypeRecipe::Bool]),
            &TypeEnv::default()
        )
        .is_none());
}

#[test]
fn pack_signatures_reject_wrong_value_arity_and_sorts() {
    let mut vocabulary = Vocabulary::default();
    register(&mut vocabulary, family(1));
    let integer = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Int));
    assert!(vocabulary
        .pack_product(family(1), &[], vec![p("x"), p("b")])
        .is_none());
    assert!(vocabulary
        .pack_product(family(1), std::slice::from_ref(&integer), vec![p("x")])
        .is_none());
    assert!(vocabulary
        .pack_product(
            family(1),
            std::slice::from_ref(&integer),
            vec![Term::Int(0), p("b")]
        )
        .is_none());
    assert!(vocabulary
        .project_product(family(1), &[integer], Term::Bool(true))
        .is_none());
    assert!(TypeArgument::new(
        Term::var("t", Sort::TypeId),
        Term::var("d", Sort::Decoration)
    )
    .is_none());
    let integer = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Int));
    let valid = vocabulary
        .pack_product(family(1), &[integer], vec![p("x"), p("b")])
        .unwrap();
    let Term::Call { name, args, .. } = &valid else {
        unreachable!()
    };
    let wrong_return_sort = Term::call(name.clone(), args.clone(), Sort::Bool);
    assert!(vocabulary
        .bridge_axioms(&[&wrong_return_sort], &mut 100_000)
        .is_none());
    let mut old = Vec::new();
    let mut typed = Vec::new();
    valid.for_each_call(&mut |name, args| old.push((name.to_owned(), args.to_vec())));
    valid.for_each_typed_call(&mut |name, args, _| typed.push((name.to_owned(), args.to_vec())));
    assert_eq!(old, typed);
}

#[test]
fn full_nominal_argument_and_decoration_vectors_do_not_collapse() {
    let mut vocabulary = Vocabulary::default();
    for f in [family(1), family(2)] {
        register(&mut vocabulary, f);
    }
    let integer = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Int));
    let natural = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Nat));
    let borrowed = argument(
        &mut vocabulary,
        TypeRecipe::SharedRef(Box::new(TypeRecipe::Int(IntRange::Int))),
    );
    assert_eq!(integer.identity(), borrowed.identity());
    assert_ne!(integer.terms(), borrowed.terms());
    let fields = vec![p("x"), p("b")];
    let first = vocabulary
        .pack_product(family(1), std::slice::from_ref(&integer), fields.clone())
        .unwrap();
    assert_ne!(
        first,
        vocabulary
            .pack_product(family(2), &[integer], fields.clone())
            .unwrap()
    );
    assert_ne!(
        first,
        vocabulary
            .pack_product(family(1), &[natural], fields.clone())
            .unwrap()
    );
    assert_ne!(
        first,
        vocabulary
            .pack_product(family(1), &[borrowed], fields)
            .unwrap()
    );
}

#[test]
fn zero_child_and_phantom_products_retain_their_full_identity() {
    let mut vocabulary = Vocabulary::default();
    assert!(vocabulary
        .register_product(ProductFamily::Unit, 0, vec![])
        .is_some());
    assert!(vocabulary.register_product(family(1), 1, vec![]).is_some());
    assert!(vocabulary.register_product(family(2), 1, vec![]).is_some());
    let integer = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Int));
    let boolean = argument(&mut vocabulary, TypeRecipe::Bool);
    let unit = vocabulary
        .pack_product(ProductFamily::Unit, &[], vec![])
        .unwrap();
    let empty = vocabulary
        .pack_product(family(1), std::slice::from_ref(&integer), vec![])
        .unwrap();
    assert_ne!(unit, empty);
    assert_ne!(
        empty,
        vocabulary
            .pack_product(family(1), &[boolean], vec![])
            .unwrap()
    );
    assert_ne!(
        empty,
        vocabulary
            .pack_product(family(2), &[integer], vec![])
            .unwrap()
    );
}

#[test]
fn untyped_products_get_only_guarded_projection_and_roundtrip_laws() {
    let mut vocabulary = Vocabulary::default();
    assert!(vocabulary
        .register_product(family(1), 0, vec![TypeRecipe::Int(IntRange::Nat)])
        .is_some());
    let value = p("untyped");
    let fields = vocabulary
        .project_product(family(1), &[], value.clone())
        .unwrap();
    let natural = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Nat));
    let unboxed = vocabulary
        .unbox_value(
            Sort::Int,
            natural.identity().clone(),
            (Some(0), None),
            fields[0].clone(),
        )
        .unwrap();
    let facts = vocabulary.bridge_axioms(&[&unboxed], &mut 100_000).unwrap();
    let schema = vocabulary.products.schemas[0].clone();
    let identity = vocabulary.call(schema.type_constructor, vec![], Sort::TypeId);
    let member = vocabulary.membership(value.clone(), identity).unwrap();
    let child_member = vocabulary
        .membership(fields[0].clone(), natural.identity().clone())
        .unwrap();
    let reconstruction = vocabulary.pack_product(family(1), &[], fields).unwrap();
    assert!(facts.contains(&Term::implies(
        member.clone(),
        Term::eq(reconstruction.clone(), value.clone())
    )));
    assert!(facts.contains(&Term::implies(member.clone(), child_member)));
    assert!(!facts.contains(&member));
    assert!(!facts.contains(&Term::eq(reconstruction, value)));
    assert!(!facts.contains(&unboxed.within(Some(0), None)));
    assert!(vocabulary.bridge_axioms(&[&unboxed], &mut 0).is_none());
}

#[test]
fn packs_need_each_typed_child_before_they_supply_membership() {
    let mut vocabulary = Vocabulary::default();
    let f = family(1);
    assert!(vocabulary
        .register_product(f, 1, vec![parameter(f, 0)])
        .is_some());
    let natural = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Nat));
    let child = p("unknown_child");
    let packed = vocabulary
        .pack_product(f, std::slice::from_ref(&natural), vec![child.clone()])
        .unwrap();
    let facts = vocabulary.bridge_axioms(&[&packed], &mut 100_000).unwrap();
    let schema = vocabulary.products.schemas[0].clone();
    let identity = vocabulary.call(
        schema.type_constructor,
        natural.terms().to_vec(),
        Sort::TypeId,
    );
    let member = vocabulary.membership(packed, identity).unwrap();
    let typed_child = vocabulary
        .membership(child, natural.identity().clone())
        .unwrap();
    assert!(facts.contains(&Term::implies(typed_child, member.clone())));
    assert!(!facts.contains(&member));
}

#[test]
fn generic_body_substitution_reinterprets_the_registered_family_schema() {
    let mut vocabulary = Vocabulary::default();
    register(&mut vocabulary, family(1));
    let symbolic = TypeArgument::named("source_d".into(), "source_t".into());
    let source = vocabulary
        .pack_product(family(1), &[symbolic], vec![p("x"), p("b")])
        .unwrap();
    let Term::Call { name, .. } = source else {
        unreachable!()
    };
    let integer = argument(&mut vocabulary, TypeRecipe::Int(IntRange::Int));
    // No concrete schema is registered. These are the actual argument sorts
    // after a generic definition's type-vector substitution.
    let args = integer
        .terms()
        .into_iter()
        .chain([p("x"), p("b")])
        .collect();
    let instantiated = Term::call(name, args, Sort::Poly);
    let facts = vocabulary
        .bridge_axioms(&[&instantiated], &mut 100_000)
        .unwrap();
    let typed = vocabulary
        .membership(p("x"), integer.identity().clone())
        .unwrap();
    let boolean = argument(&mut vocabulary, TypeRecipe::Bool);
    let typed_bool = vocabulary
        .membership(p("b"), boolean.identity().clone())
        .unwrap();
    let schema = vocabulary.products.schemas[0].clone();
    let identity = vocabulary.call(
        schema.type_constructor,
        integer.terms().to_vec(),
        Sort::TypeId,
    );
    let member = vocabulary.membership(instantiated, identity).unwrap();
    assert!(facts.contains(&Term::implies(Term::and(vec![typed, typed_bool]), member)));
}
