//! Declaration-family and caller-binder rejection controls.
use super::*;
use crate::{AdtId, DefHash, FnId};

fn id(n: u64) -> AdtId {
    AdtId(DefHash::new(74, n))
}

#[test]
fn enum_fields_require_their_own_declaration_binders() {
    for wrong in [
        TypeRecipe::Parameter {
            owner: FnId(DefHash::new(74, 1)),
            index: 0,
        },
        TypeRecipe::ProductParameter {
            owner: ProductFamily::Enum(id(2)),
            index: 0,
        },
        TypeRecipe::ProductParameter {
            owner: ProductFamily::Enum(id(1)),
            index: 1,
        },
    ] {
        assert!(Vocabulary::default()
            .register_sum(id(1), 1, vec![vec![], vec![wrong]])
            .is_none());
    }
    let field = TypeRecipe::ProductParameter {
        owner: ProductFamily::Enum(id(1)),
        index: 0,
    };
    assert!(Vocabulary::default()
        .register_sum(id(1), 1, vec![vec![], vec![field]])
        .is_some());
}

#[test]
fn constructors_and_selector_views_retain_full_nominal_type_vectors() {
    let mut v = Vocabulary::default();
    for n in [1, 2] {
        let field = TypeRecipe::ProductParameter {
            owner: ProductFamily::Enum(id(n)),
            index: 0,
        };
        assert!(v
            .register_sum(id(n), 1, vec![vec![], vec![field]])
            .is_some());
    }
    let boolean = v.argument(&TypeRecipe::Bool, &TypeEnv::default()).unwrap();
    let integer = v
        .argument(&TypeRecipe::Int(crate::IntRange::U(8)), &TypeEnv::default())
        .unwrap();
    let a = v
        .construct_sum(id(1), std::slice::from_ref(&boolean), 0, vec![])
        .unwrap();
    let b = v
        .construct_sum(id(1), std::slice::from_ref(&integer), 0, vec![])
        .unwrap();
    let other = v
        .construct_sum(id(2), std::slice::from_ref(&boolean), 0, vec![])
        .unwrap();
    assert_ne!(a, b);
    assert_ne!(a, other);
    let pa = v
        .project_sum(id(1), std::slice::from_ref(&boolean), 1, 0, a.clone())
        .unwrap();
    let pb = v.project_sum(id(1), &[integer], 1, 0, a.clone()).unwrap();
    assert_ne!(pa, pb);
    assert!(v.construct_sum(id(1), &[], 0, vec![]).is_none());
    assert!(v.project_sum(id(1), &[boolean], 9, 0, a).is_none());
}

#[test]
fn enum_type_recipes_cannot_reinterpret_another_function_binder() {
    let actual = id(1);
    let declared = |candidate| (candidate == actual).then_some(RecipeAdt::Enum(1));
    let a = FnId(DefHash::new(74, 10));
    let b = FnId(DefHash::new(74, 11));
    let recipe = TypeRecipe::registered(
        &crate::Ty::Adt(actual, vec![crate::Ty::Param(0)]),
        Some(a),
        &declared,
            &|_| None)
    .unwrap();
    let argument = TypeArgument::named("d".into(), "t".into());
    let mut vocabulary = Vocabulary::default();
    assert!(vocabulary
        .argument(&recipe, &TypeEnv::new(a, vec![argument.clone()]))
        .is_some());
    assert!(vocabulary
        .argument(&recipe, &TypeEnv::new(b, vec![argument]))
        .is_none());
}

#[test]
fn associated_sum_fields_require_registered_members_full_binders_and_same_work() {
    use std::cell::Cell;
    let member = crate::ProjectionId(DefHash::new(740, 1));
    let family = ProductFamily::Enum(id(3));
    let field = TypeRecipe::Projection(member, vec![TypeRecipe::ProductParameter { owner: family, index: 0 }]);
    let mut vocabulary = Vocabulary::default();
    let work = Cell::new(100_000);
    assert!(vocabulary.register_sum_with_work(id(3), 1, vec![vec![], vec![field.clone()]], &work, crate::SpanId(0)).unwrap().is_none());
    vocabulary.register_projection_declaration(member, 1).unwrap();
    let wrong = TypeRecipe::Projection(member, vec![TypeRecipe::ProductParameter { owner: ProductFamily::Enum(id(4)), index: 0 }]);
    assert!(vocabulary.register_sum_with_work(id(3), 1, vec![vec![], vec![wrong]], &work, crate::SpanId(0)).unwrap().is_none());
    assert!(vocabulary.register_sum(id(3), 1, vec![vec![], vec![field.clone()]]).is_none());
    vocabulary.register_sum_with_work(id(3), 1, vec![vec![], vec![field]], &work, crate::SpanId(0)).unwrap().unwrap();
    let argument = vocabulary.argument(&TypeRecipe::Bool, &TypeEnv::default()).unwrap();
    assert!(vocabulary.construct_sum(id(3), &[argument.clone()], 0, vec![]).is_none());
    let value = vocabulary.construct_sum_with_work(id(3), &[argument.clone()], 0, vec![], &work, crate::SpanId(0)).unwrap().unwrap();
    // A selector from the inactive variant stays a total, unspecified view.
    // Its presence must never supply an unconditional active-variant fact.
    let selected = vocabulary.project_sum_with_work(id(3), &[argument.clone()], 1, 0, value.clone(), &work, crate::SpanId(0)).unwrap().unwrap();
    let test = vocabulary.test_sum_with_work(id(3), &[argument.clone()], 1, value.clone(), &work, crate::SpanId(0)).unwrap().unwrap();
    let facts = vocabulary.bridge_axioms(&[&selected, &test], &mut 100_000).unwrap();
    assert!(!facts.contains(&test));
    assert!(!facts.contains(&Term::Bool(false)));
    assert!(facts.iter().any(|fact| matches!(fact, Term::Implies(_, _))));
    assert!(vocabulary.bridge_axioms(&[&selected], &mut 0).is_none());
    work.set(0);
    assert!(vocabulary.project_sum_with_work(id(3), &[argument], 1, 0, value, &work, crate::SpanId(0)).is_err());
    assert_eq!(work.get(), 0);
}
