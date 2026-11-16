//! Behavioral controls for the private correspondence relation only. These
//! DATA observations cannot mint the native inputs or an import capability.

use super::*;
use crate::declaration_alignment::TypeParameter;

fn key(krate: u64, index: u64) -> NativeKey {
    NativeKey {
        stable_crate_id: krate,
        def_path_hash: (u128::from(krate) << 64) | u128::from(index),
    }
}

fn anchor(index: u32) -> Anchor {
    Anchor::Named(SourceAnchor {
        identifier: AuthoredSpan {
            relative_file: "source/vstd/trait.rs".into(),
            file_sha256: [3; 32],
            original_file_len: 1000,
            bytes: (index * 10, index * 10 + 1),
        },
        enclosing_declarations: Vec::new(),
    })
}

fn scopes(parent: u32, own: u32) -> Vec<GenericScope> {
    let scope = |parent, own| GenericScope {
        parent_count: parent,
        own_type_parameters: (0..own)
            .map(|offset| TypeParameter {
                index: parent + offset,
                has_default: false,
                synthetic: false,
                pure_wrt_drop: false,
            })
            .collect(),
        has_self: false,
    };
    if parent == 0 {
        vec![scope(0, own)]
    } else {
        vec![scope(parent, own), scope(0, parent)]
    }
}

fn view(krate: u64) -> View {
    let mut entries = BTreeMap::new();
    let mut insert = |index, shape, generics| {
        entries.insert(
            key(krate, index),
            Observation::Observed(Entry {
                anchor: anchor(index as u32),
                generics,
                clauses: Vec::new(),
                shape,
            }),
        );
    };
    insert(1, Shape::Trait, scopes(0, 2));
    for index in [2, 3] {
        insert(
            index,
            Shape::Function {
                origin: Origin::Trait(key(krate, 1)),
                inputs: vec![DeclarationType::Parameter(0)],
                output: DeclarationType::Parameter(1),
            },
            scopes(2, 0),
        );
    }
    insert(
        4,
        Shape::Implementation {
            declaration: Reference {
                key: key(krate, 1),
                artifact: None,
            },
            arguments: vec![
                DeclarationType::Integer {
                    signed: false,
                    width: alignment::IntegerWidth::Fixed(8),
                },
                DeclarationType::Parameter(0),
            ],
        },
        scopes(0, 1),
    );
    insert(
        5,
        Shape::Function {
            origin: Origin::ExplicitImpl {
                implementation: key(krate, 4),
                declaration: key(krate, 2),
            },
            inputs: vec![DeclarationType::Integer {
                signed: false,
                width: alignment::IntegerWidth::Fixed(8),
            }],
            output: DeclarationType::Parameter(0),
        },
        scopes(1, 0),
    );
    View { entries }
}

fn entry(view: &mut View, krate: u64, index: u64) -> &mut Entry {
    let Observation::Observed(entry) = view.entries.get_mut(&key(krate, index)).unwrap() else {
        panic!()
    };
    entry
}

fn compare(a: &View, b: &View) -> Pairs {
    Pairs::compare(a, b, &BTreeSet::new(), BTreeMap::new()).unwrap()
}

#[test]
fn native_key_changes_preserve_full_trait_member_relationships() {
    let a = view(10);
    let b = view(20);
    let pairs = compare(&a, &b);
    for index in 1..=5 {
        assert_eq!(pairs.erase(key(10, index)), Some(&key(20, index)));
    }
}

#[test]
fn same_signature_other_trait_member_cannot_replace_selected_declaration() {
    let a = view(10);
    let mut b = view(20);
    let Shape::Function {
        origin: Origin::ExplicitImpl { declaration, .. },
        ..
    } = &mut entry(&mut b, 20, 5).shape
    else {
        panic!()
    };
    *declaration = key(20, 3);
    assert_eq!(compare(&a, &b).erase(key(10, 5)), None);
}

#[test]
fn reordered_impl_arguments_and_changed_clause_remove_dependent_members() {
    let a = view(10);
    let mut b = view(20);
    let Shape::Implementation { arguments, .. } = &mut entry(&mut b, 20, 4).shape else {
        panic!()
    };
    arguments.swap(0, 1);
    let pairs = compare(&a, &b);
    assert_eq!(pairs.erase(key(10, 4)), None);
    assert_eq!(pairs.erase(key(10, 5)), None);
    let mut b = view(20);
    entry(&mut b, 20, 1).clauses.push(Bound {
        scope: Reference {
            key: key(20, 1),
            artifact: None,
        },
        declaration: Reference {
            key: key(99, 1),
            artifact: Some([1; 32]),
        },
        arguments: vec![DeclarationType::Parameter(0)],
    });
    let pairs = compare(&a, &b);
    for index in 1..=5 {
        assert_eq!(pairs.erase(key(10, index)), None);
    }
}

#[test]
fn changed_source_duplicate_anchor_or_metadata_roundtrip_never_supplies_a_pair() {
    let a = view(10);
    let mut b = view(20);
    entry(&mut b, 20, 5).anchor = anchor(99);
    assert_eq!(compare(&a, &b).erase(key(10, 5)), None);
    let mut b = view(20);
    entry(&mut b, 20, 3).anchor = anchor(2);
    assert_eq!(compare(&a, &b).erase(key(10, 2)), None);
    let mut loaded = view(20);
    loaded.entries.remove(&key(20, 4));
    let missing = roundtrip(&view(20), &loaded);
    assert!(missing.contains(&key(20, 4)));
    let pairs = Pairs::compare(&a, &view(20), &missing, BTreeMap::new()).unwrap();
    assert_eq!(pairs.erase(key(10, 5)), None);
}

fn inherent_view(krate: u64) -> View {
    let carrier = DeclarationType::LocalNominal {
        declaration: key(krate, 9),
        arguments: vec![DeclarationType::Parameter(0)],
    };
    let bound = Bound {
        scope: Reference {
            key: key(krate, 1),
            artifact: None,
        },
        declaration: Reference {
            key: key(99, 1),
            artifact: Some([1; 32]),
        },
        arguments: vec![DeclarationType::Parameter(0)],
    };
    let Anchor::Named(source) = anchor(1) else {
        panic!()
    };
    View {
        entries: BTreeMap::from([
            (
                key(krate, 1),
                Observation::Observed(Entry {
                    anchor: Anchor::Implementation(source.identifier),
                    generics: scopes(0, 1),
                    clauses: vec![bound.clone()],
                    shape: Shape::InherentImplementation {
                        self_type: carrier.clone(),
                    },
                }),
            ),
            (
                key(krate, 2),
                Observation::Observed(Entry {
                    anchor: anchor(2),
                    generics: scopes(1, 0),
                    clauses: vec![bound],
                    shape: Shape::Function {
                        origin: Origin::Inherent {
                            implementation: key(krate, 1),
                            self_type: carrier.clone(),
                        },
                        inputs: vec![carrier],
                        output: DeclarationType::Parameter(0),
                    },
                }),
            ),
        ]),
    }
}

fn compare_inherent(a: &View, b: &View) -> Pairs {
    Pairs::compare(
        a,
        b,
        &BTreeSet::new(),
        BTreeMap::from([(key(10, 9), key(20, 9))]),
    )
    .unwrap()
}

#[test]
fn generic_inherent_methods_require_their_complete_native_parent_scope() {
    let a = inherent_view(10);
    let b = inherent_view(20);
    let pairs = compare_inherent(&a, &b);
    assert_eq!(pairs.erase(key(10, 1)), Some(&key(20, 1)));
    assert_eq!(pairs.erase(key(10, 2)), Some(&key(20, 2)));
    let mut missing = inherent_view(20);
    missing.entries.remove(&key(20, 1));
    assert_eq!(compare_inherent(&a, &missing).erase(key(10, 2)), None);
    // Signature equality alone cannot stand in for the native impl owner.
    let mut other = inherent_view(20);
    let Shape::Function {
        origin: Origin::Inherent { implementation, .. },
        ..
    } = &mut entry(&mut other, 20, 2).shape
    else {
        panic!()
    };
    *implementation = key(20, 3);
    assert_eq!(compare_inherent(&a, &other).erase(key(10, 2)), None);
    assert_eq!(compare(&a, &b).erase(key(10, 2)), None);
}

#[test]
fn inherent_parent_binder_self_type_and_bound_changes_remove_method_pairs() {
    let a = inherent_view(10);
    let mut b = inherent_view(20);
    entry(&mut b, 20, 1).generics = scopes(0, 2);
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
    let mut b = inherent_view(20);
    let Shape::InherentImplementation { self_type } = &mut entry(&mut b, 20, 1).shape else {
        panic!()
    };
    *self_type = DeclarationType::LocalNominal {
        declaration: key(20, 8),
        arguments: vec![DeclarationType::Parameter(0)],
    };
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
    let mut b = inherent_view(20);
    entry(&mut b, 20, 1).clauses[0].declaration.artifact = Some([2; 32]);
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
    let mut b = inherent_view(20);
    entry(&mut b, 20, 2).clauses[0].scope.key = key(20, 3);
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
}

#[test]
fn inherent_scope_requires_original_source_and_actual_metadata_roundtrip() {
    let a = inherent_view(10);
    let mut b = inherent_view(20);
    entry(&mut b, 20, 1).anchor = anchor(9);
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
    let mut b = inherent_view(20);
    let duplicate = entry(&mut b, 20, 1).clone();
    b.entries
        .insert(key(20, 3), Observation::Observed(duplicate));
    assert_eq!(compare_inherent(&a, &b).erase(key(10, 2)), None);
    let b = inherent_view(20);
    let mut loaded = inherent_view(20);
    entry(&mut loaded, 20, 1).clauses.clear();
    let missing = roundtrip(&b, &loaded);
    assert!(missing.contains(&key(20, 1)));
    let pairs =
        Pairs::compare(&a, &b, &missing, BTreeMap::from([(key(10, 9), key(20, 9))])).unwrap();
    assert_eq!(pairs.erase(key(10, 2)), None);
}
