// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for TrustVcType parsing, serialization, and round-trip properties.
//!
//! Covers all branches in `ir_type_parse.rs`: primitives, collections, SpecFn,
//! Option/Result/List/Tree datatypes, Ghost/Tracked/Proph/Snapshot erasure,
//! type parameters, strict vs lossy mode, and edge cases.

use super::*;

fn roundtrip(input: &str) {
    let parsed = TrustVcType::try_from_str(input).unwrap_or_else(|e| panic!("{input}: {e}"));
    let serialized = parsed.to_type_string();
    let reparsed =
        TrustVcType::try_from_str(&serialized).unwrap_or_else(|e| panic!("{serialized}: {e}"));
    assert_eq!(parsed, reparsed, "round-trip failed for {input}");
}

#[test]
fn test_primitive_types_roundtrip() {
    for ty in [
        "()", "bool", "char", "str", "String", "i8", "i16", "i32", "i64", "i128", "u8", "u16",
        "u32", "u64", "u128", "f32", "f64", "real", "int", "nat",
    ] {
        roundtrip(ty);
    }
}

#[test]
fn test_unit_type_properties() {
    let parsed = TrustVcType::try_from_str("()").unwrap();
    assert_eq!(parsed, TrustVcType::Unit);
    assert_eq!(parsed.to_type_string(), "()");
    assert_eq!(parsed.bit_width(), None);
    assert!(!parsed.contains_opaque());
    assert!(!parsed.contains_float());
    assert!(!parsed.is_collection());
}

#[test]
fn test_phantom_data_parses_to_unit() {
    // `PhantomData<T>` is a zero-sized, one-inhabitant marker isomorphic to the
    // unit type, so it erases to `Unit` regardless of `T` (cluster #2779).
    for ty in [
        "PhantomData<u64>",
        "PhantomData<i32>",
        "core::marker::PhantomData<u64>",
        "std::marker::PhantomData<bool>",
        "PhantomData<Seq<u8>>",
    ] {
        assert_eq!(
            TrustVcType::try_from_str(ty).unwrap(),
            TrustVcType::Unit,
            "{ty} should erase to Unit"
        );
    }
}

#[test]
fn test_phantom_data_inner_type_still_validated_under_strict() {
    // The inner `T` is parsed even though it is erased, so an unknown inner
    // type fails closed under strict parsing rather than being silently
    // accepted. This keeps the verifier from minting a Unit out of garbage.
    let err = TrustVcType::try_from_str("PhantomData<NotAType>").unwrap_err();
    assert!(
        matches!(err, TrustVcTypeParseError::UnknownType { .. }),
        "unknown PhantomData inner type should fail closed, got: {err:?}"
    );
}

#[test]
fn test_phantom_data_without_type_args_is_not_unit() {
    // Bare `PhantomData` (no `<...>`) is not a recognized type spelling; it is
    // an unknown nominal type and must fail closed under strict parsing rather
    // than collapse to Unit.
    let err = TrustVcType::try_from_str("PhantomData").unwrap_err();
    assert!(
        matches!(err, TrustVcTypeParseError::UnknownType { .. }),
        "bare PhantomData should fail closed, got: {err:?}"
    );
}

#[test]
fn test_string_aliases_parse_to_string() {
    for alias in ["String", "alloc::string::String", "std::string::String"] {
        assert_eq!(
            TrustVcType::try_from_str(alias).unwrap(),
            TrustVcType::String
        );
    }
}

#[test]
fn test_collection_types_roundtrip() {
    for ty in [
        "Seq<i32>",
        "Set<bool>",
        "Multiset<u64>",
        "Map<String, i32>",
        "Seq<Set<i32>>",
        "Map<u32, Seq<bool>>",
    ] {
        roundtrip(ty);
    }
}

#[test]
fn test_tuple_types_parse_inside_arrays() {
    let tuple_ty = TrustVcType::try_from_str("(u64, u64)").unwrap();
    let TrustVcType::Datatype { name, variants } = tuple_ty else {
        panic!("tuple should parse to datatype");
    };
    assert_eq!(name, "(u64, u64)");
    assert_eq!(variants.len(), 1);
    assert_eq!(variants[0].name, "Tuple");
    assert_eq!(
        variants[0].fields,
        vec![
            ("0".to_string(), TrustVcType::Uint { width: 64 }),
            ("1".to_string(), TrustVcType::Uint { width: 64 }),
        ]
    );

    let array_ty = TrustVcType::try_from_str("[(u64, u64); 3]").unwrap();
    let TrustVcType::Array(element_ty, 3) = array_ty else {
        panic!("array of tuples should parse as fixed array");
    };
    assert!(matches!(
        element_ty.as_ref(),
        TrustVcType::Datatype { name, .. } if name == "(u64, u64)"
    ));
    roundtrip("[(u64, u64); 3]");
}

#[test]
fn test_std_collection_maps_parse_to_trust_vc_map() {
    let expected = TrustVcType::Map(
        Box::new(TrustVcType::String),
        Box::new(TrustVcType::Int { width: 32 }),
    );

    for ty in [
        "HashMap<String, i32>",
        "BTreeMap<String, i32>",
        "std::collections::HashMap<String, i32>",
        "std::collections::hash_map::HashMap<String, i32>",
        "std::collections::BTreeMap<String, i32>",
        "std::collections::btree_map::BTreeMap<String, i32>",
        "alloc::collections::BTreeMap<String, i32>",
        "alloc::collections::btree_map::BTreeMap<String, i32>",
    ] {
        assert_eq!(TrustVcType::try_from_str(ty).unwrap(), expected, "{ty}");
    }
}

#[test]
fn test_std_collection_sets_parse_to_trust_vc_set() {
    let expected = TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 }));

    for ty in [
        "HashSet<u64>",
        "BTreeSet<u64>",
        "std::collections::HashSet<u64>",
        "std::collections::hash_set::HashSet<u64>",
        "std::collections::BTreeSet<u64>",
        "std::collections::btree_set::BTreeSet<u64>",
        "alloc::collections::BTreeSet<u64>",
        "alloc::collections::btree_set::BTreeSet<u64>",
    ] {
        assert_eq!(TrustVcType::try_from_str(ty).unwrap(), expected, "{ty}");
    }
}

#[test]
fn test_std_collection_aliases_preserve_strict_matching() {
    for ty in [
        "MyHashMap<String, i32>",
        "my::collections::HashMap<String, i32>",
        "std::collections::LinkedList<i32>",
        "alloc::collections::HashMap<String, i32>",
    ] {
        assert!(
            matches!(
                TrustVcType::try_from_str(ty),
                Err(TrustVcTypeParseError::UnknownType { .. })
            ),
            "{ty} should remain unknown"
        );
    }
}

#[test]
fn test_std_collection_aliases_parse_nested_types() {
    assert_eq!(
        TrustVcType::try_from_str(
            "std::collections::HashMap<String, alloc::collections::BTreeSet<u64>>"
        )
        .unwrap(),
        TrustVcType::Map(
            Box::new(TrustVcType::String),
            Box::new(TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })))
        )
    );
}

#[test]
fn test_spec_fn_single_arg() {
    let parsed = TrustVcType::try_from_str("SpecFn<i32, bool>").unwrap();
    match &parsed {
        TrustVcType::SpecFn(args, ret) => {
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], TrustVcType::Int { width: 32 });
            assert_eq!(**ret, TrustVcType::Bool);
        }
        other => panic!("expected SpecFn, got {other:?}"),
    }
    roundtrip("SpecFn<i32, bool>");
}

#[test]
fn test_spec_fn_tuple_args() {
    let parsed = TrustVcType::try_from_str("SpecFn<(i32, u64), bool>").unwrap();
    match &parsed {
        TrustVcType::SpecFn(args, _) => assert_eq!(args.len(), 2),
        other => panic!("expected SpecFn, got {other:?}"),
    }
}

#[test]
fn test_spec_fn_unit_arg_roundtrip() {
    let ty = TrustVcType::SpecFn(vec![TrustVcType::Unit], Box::new(TrustVcType::Bool));
    let serialized = ty.to_type_string();
    assert_eq!(serialized, "SpecFn<((),), bool>");
    assert_eq!(TrustVcType::try_from_str(&serialized).unwrap(), ty);
}

#[test]
fn test_option_parses_to_datatype() {
    let parsed = TrustVcType::try_from_str("Option<i32>").unwrap();
    match &parsed {
        TrustVcType::Datatype { name, variants } => {
            assert_eq!(name, "Option<i32>");
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].name, "None");
            assert_eq!(variants[1].name, "Some");
        }
        other => panic!("expected Datatype, got {other:?}"),
    }
}

#[test]
fn test_option_reference_erases_to_value_type() {
    let parsed = TrustVcType::try_from_str("Option<&u32>").unwrap();
    assert_eq!(parsed, TrustVcType::try_from_str("Option<u32>").unwrap());
}

#[test]
fn test_references_with_lifetimes_erase_to_value_type() {
    assert_eq!(
        TrustVcType::try_from_str("Option<&'a u32>").unwrap(),
        TrustVcType::try_from_str("Option<u32>").unwrap()
    );
    assert_eq!(
        TrustVcType::try_from_str("Option<&'a mut u32>").unwrap(),
        TrustVcType::try_from_str("Option<u32>").unwrap()
    );
    assert_eq!(
        TrustVcType::try_from_str("Option<&'static ()>").unwrap(),
        TrustVcType::try_from_str("Option<()>").unwrap()
    );
    assert_eq!(
        TrustVcType::try_from_str("Result<&'a (), ()>").unwrap(),
        TrustVcType::try_from_str("Result<(), ()>").unwrap()
    );
}

#[test]
fn test_result_parses_to_datatype() {
    let parsed = TrustVcType::try_from_str("Result<u32, String>").unwrap();
    match &parsed {
        TrustVcType::Datatype { name, variants } => {
            assert_eq!(name, "Result<u32, String>");
            assert_eq!(variants[0].name, "Ok");
            assert_eq!(variants[1].name, "Err");
        }
        other => panic!("expected Datatype, got {other:?}"),
    }
}

#[test]
fn test_cow_parses_lifetime_erased_inner_type() {
    let parsed = TrustVcType::try_from_str("Cow<'_, str>").unwrap();
    match &parsed {
        TrustVcType::Datatype { name, variants } => {
            assert_eq!(name, "Cow<str>");
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].name, "Borrowed");
            assert_eq!(variants[1].name, "Owned");
            assert_eq!(parsed.cow_inner_type(), Some(TrustVcType::StrSlice));
            assert_eq!(
                parsed.cow_view_type(),
                Some(TrustVcType::Seq(Box::new(TrustVcType::Char)))
            );
        }
        other => panic!("expected Datatype, got {other:?}"),
    }
}

#[test]
fn test_cow_aliases_parse_to_canonical_cow_type() {
    for alias in [
        "Cow<'a, String>",
        "std::borrow::Cow<'a, String>",
        "alloc::borrow::Cow<'a, String>",
        "core::borrow::Cow<'a, String>",
    ] {
        assert_eq!(
            TrustVcType::try_from_str(alias).unwrap().to_type_string(),
            "Cow<String>"
        );
    }
}

#[test]
fn test_recursive_list_and_tree() {
    let list = TrustVcType::try_from_str("List<i32>").unwrap();
    match &list {
        TrustVcType::Datatype { variants, .. } => {
            assert_eq!(variants[0].name, "Nil");
            assert_eq!(variants[1].name, "Cons");
            assert!(matches!(
                &variants[1].fields[1].1,
                TrustVcType::RecursiveRef(_)
            ));
        }
        other => panic!("expected Datatype, got {other:?}"),
    }
    let tree = TrustVcType::try_from_str("Tree<bool>").unwrap();
    match &tree {
        TrustVcType::Datatype { variants, .. } => {
            assert_eq!(variants[0].name, "Leaf");
            assert_eq!(variants[1].name, "Branch");
        }
        other => panic!("expected Datatype, got {other:?}"),
    }
}

#[test]
fn test_ghost_tracked_proph_snapshot_erase_to_inner() {
    for (wrapper, inner) in [
        ("Ghost<i32>", "i32"),
        ("Tracked<u64>", "u64"),
        ("Proph<bool>", "bool"),
        ("Snapshot<Seq<i32>>", "Seq<i32>"),
    ] {
        let parsed = TrustVcType::try_from_str(wrapper).unwrap();
        let expected = TrustVcType::try_from_str(inner).unwrap();
        assert_eq!(parsed, expected, "{wrapper} should erase to {inner}");
    }
}

#[test]
fn test_type_params_recognized() {
    assert_eq!(
        TrustVcType::try_from_str("T").unwrap(),
        TrustVcType::TypeParam("T".to_string())
    );
    assert_eq!(
        TrustVcType::try_from_str("AB").unwrap(),
        TrustVcType::TypeParam("AB".to_string())
    );
    assert!(
        TrustVcType::try_from_str("ABC").is_err(),
        ">2 chars not a type param"
    );
    assert!(
        TrustVcType::try_from_str("a").is_err(),
        "lowercase not a type param"
    );
}

#[test]
fn test_strict_rejects_unknown_types() {
    let err = TrustVcType::try_from_str("MyStruct").unwrap_err();
    assert!(matches!(err, TrustVcTypeParseError::UnknownType { .. }));
}

#[test]
fn test_lossy_accepts_unknown_as_opaque() {
    let parsed = TrustVcType::parse_or_opaque("MyStruct");
    assert_eq!(parsed, TrustVcType::Opaque("MyStruct".to_string()));
}

#[test]
fn test_empty_string_rejected() {
    let err = TrustVcType::try_from_str("").unwrap_err();
    assert!(matches!(err, TrustVcTypeParseError::EmptyTypeString));
}

#[test]
fn test_whitespace_trimmed() {
    assert_eq!(
        TrustVcType::try_from_str("  i32  ").unwrap(),
        TrustVcType::Int { width: 32 }
    );
}

#[test]
fn test_isize_usize_use_pointer_width() {
    let isize_ty = TrustVcType::try_from_str("isize").unwrap();
    let usize_ty = TrustVcType::try_from_str("usize").unwrap();
    let w = pointer_width();
    assert_eq!(isize_ty, TrustVcType::Int { width: w });
    assert_eq!(usize_ty, TrustVcType::Uint { width: w });
}

#[test]
fn strict_array_type_parser_rejects_symbolic_const_length() {
    let err = TrustVcType::try_from_str("[u8; CONST_ARRAY_LEN]").unwrap_err();
    assert!(
        matches!(err, TrustVcTypeParseError::InvalidSyntax { kind, .. } if kind == "array length"),
        "symbolic const array lengths should be resolved only by source-aware extraction, got: {err:?}"
    );
}
