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
    )
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
