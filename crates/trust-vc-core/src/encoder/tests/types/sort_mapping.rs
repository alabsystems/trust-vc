// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort translation tests: sort_for_type, quantifier_sort_for_type, polymorphism.

use super::*;

// ========================================================================
// sort translation helpers
// ========================================================================

#[test]
fn test_sort_for_type_bool() {
    assert_eq!(sort_for_type(&TrustVcType::Bool), Sort::Bool);
}

#[test]
fn test_sort_for_type_signed_int() {
    assert_eq!(
        sort_for_type(&TrustVcType::Int { width: 8 }),
        Sort::bitvec(8)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Int { width: 32 }),
        Sort::bitvec(32)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Int { width: 64 }),
        Sort::bitvec(64)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Int { width: 128 }),
        Sort::bitvec(128)
    );
}

#[test]
fn test_sort_for_type_unsigned_int() {
    assert_eq!(
        sort_for_type(&TrustVcType::Uint { width: 8 }),
        Sort::bitvec(8)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Uint { width: 32 }),
        Sort::bitvec(32)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Uint { width: 64 }),
        Sort::bitvec(64)
    );
}

#[test]
fn test_sort_for_type_math_int() {
    assert_eq!(sort_for_type(&TrustVcType::MathInt), Sort::Int);
}

#[test]
fn test_sort_for_type_char() {
    assert_eq!(sort_for_type(&TrustVcType::Char), Sort::bitvec(32));
}

#[test]
fn test_sort_for_type_nat_is_int() {
    assert_eq!(sort_for_type(&TrustVcType::Nat), Sort::Int);
}

#[test]
fn test_quantifier_sort_nat_becomes_int() {
    assert_eq!(quantifier_sort_for_type(&TrustVcType::Nat), Sort::Int);
}

#[test]
fn test_sort_for_type_real() {
    assert_eq!(sort_for_type(&TrustVcType::Real), Sort::Real);
}

#[test]
fn test_sort_for_type_float_uses_native_fp() {
    assert_eq!(
        sort_for_type(&TrustVcType::Float { width: 32 }),
        Sort::FloatingPoint(8, 24)
    );
    assert_eq!(
        sort_for_type(&TrustVcType::Float { width: 64 }),
        Sort::FloatingPoint(11, 53)
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_sort_for_type_seq() {
    let sort = sort_for_type(&TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Seq");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(pointer_width()));
    assert_eq!(arr.element_sort, Sort::bitvec(32));
}

#[cfg(feature = "native-seq")]
#[test]
fn test_sort_for_type_seq_uses_native_seq_sort() {
    let sort = sort_for_type(&TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })));
    assert_eq!(sort, Sort::seq(Sort::bitvec(32)));
}

#[test]
#[cfg(all(not(feature = "native-strings"), not(feature = "native-seq")))]
fn test_sort_for_type_string_like_matches_seq_char_backend() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = sort_for_type(&ty);
        let Sort::Array(arr) = &sort else {
            panic!("expected Array sort for string-like type");
        };
        assert_eq!(arr.index_sort, Sort::bitvec(pointer_width()));
        assert_eq!(arr.element_sort, Sort::bitvec(32));
    }
}

#[test]
#[cfg(all(not(feature = "native-strings"), feature = "native-seq"))]
fn test_sort_for_type_string_like_maps_to_native_seq() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = sort_for_type(&ty);
        assert_eq!(sort, Sort::seq(Sort::bitvec(32)));
    }
}

#[test]
#[cfg(feature = "native-strings")]
fn test_sort_for_type_string_like_maps_to_native_string_sort() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = sort_for_type(&ty);
        assert_eq!(sort, Sort::String);
    }
}

#[test]
fn test_sort_for_type_set() {
    let sort = sort_for_type(&TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Set");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(64));
    assert_eq!(arr.element_sort, Sort::Bool);
}

#[test]
fn test_sort_for_type_multiset() {
    let sort = sort_for_type(&TrustVcType::Multiset(Box::new(TrustVcType::Uint {
        width: 64,
    })));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Multiset");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(64));
    assert_eq!(arr.element_sort, Sort::Int);
}

#[test]
fn test_sort_for_type_map() {
    let sort = sort_for_type(&TrustVcType::Map(
        Box::new(TrustVcType::Int { width: 32 }),
        Box::new(TrustVcType::Bool),
    ));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Map");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(32));
    assert_eq!(arr.element_sort, Sort::Bool);
}

#[test]
fn test_sort_for_type_builtin_datatype_is_native_carrier() {
    // Native-datatype migration: builtin datatypes no longer share the legacy
    // `Sort::Int` carrier; each maps to its own native carrier sort
    // `Sort::Uninterpreted(name)` (the term-level form of `Sort::Datatype`).
    use crate::encoder::datatype::datatype_carrier_sort;
    assert_eq!(
        sort_for_type(&TrustVcType::from_str("Option<u64>").unwrap()),
        datatype_carrier_sort("Option<u64>")
    );
    assert_eq!(
        sort_for_type(&TrustVcType::from_str("Result<u32, bool>").unwrap()),
        datatype_carrier_sort("Result<u32, bool>")
    );
}

#[test]
fn test_sort_for_type_opaque_is_int() {
    assert_eq!(
        sort_for_type(&TrustVcType::Opaque("String".to_string())),
        Sort::Int
    );
}

/// Signed and unsigned integers of the same width map to the same BV sort.
/// This is correct because signedness is tracked by TrustVcType, not by ay sort.
#[test]
fn test_sort_for_type_signed_unsigned_same_sort() {
    assert_eq!(
        sort_for_type(&TrustVcType::Int { width: 32 }),
        sort_for_type(&TrustVcType::Uint { width: 32 }),
        "i32 and u32 must map to the same BV(32) sort"
    );
}

#[test]
fn test_quantifier_sort_integers_become_int() {
    let types = [
        TrustVcType::Int { width: 8 },
        TrustVcType::Int { width: 32 },
        TrustVcType::Uint { width: 64 },
        TrustVcType::MathInt,
    ];
    for ty in &types {
        assert_eq!(quantifier_sort_for_type(ty), Sort::Int);
    }
}

#[test]
fn test_quantifier_sort_bool_and_real_stay_scalar() {
    assert_eq!(quantifier_sort_for_type(&TrustVcType::Bool), Sort::Bool);
    assert_eq!(quantifier_sort_for_type(&TrustVcType::Real), Sort::Real);
}

#[test]
fn test_quantifier_sort_float_preserves_fp_precision() {
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Float { width: 32 }),
        Sort::FloatingPoint(8, 24)
    );
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Float { width: 64 }),
        Sort::FloatingPoint(11, 53)
    );
}

/// Char maps to Sort::Int in quantifier contexts (consistent with Uint{32})
/// to avoid sort mismatch with int-mode arithmetic. Fixes #2564.
#[test]
fn test_quantifier_sort_char_is_int() {
    assert_eq!(quantifier_sort_for_type(&TrustVcType::Char), Sort::Int);
}

#[test]
#[cfg(all(not(feature = "native-strings"), not(feature = "native-seq")))]
fn test_quantifier_sort_string_like_uses_int_index_and_int_elements() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = quantifier_sort_for_type(&ty);
        let Sort::Array(arr) = &sort else {
            panic!("expected Array sort for quantifier string-like type");
        };
        assert_eq!(arr.index_sort, Sort::Int);
        // Element sort is Int in quantifier context (consistent with Char → Int).
        assert_eq!(arr.element_sort, Sort::Int);
    }
}

#[test]
#[cfg(all(not(feature = "native-strings"), feature = "native-seq"))]
fn test_quantifier_sort_string_like_maps_to_native_seq() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = quantifier_sort_for_type(&ty);
        // Under native-seq, strings keep Seq(BV(32)) in quantifier context
        // to match non-quantifier string variables (#2680 Slice 3).
        assert_eq!(sort, Sort::seq(Sort::bitvec(32)));
    }
}

#[test]
#[cfg(feature = "native-strings")]
fn test_quantifier_sort_string_like_maps_to_native_string_sort() {
    for ty in [TrustVcType::StrSlice, TrustVcType::String] {
        let sort = quantifier_sort_for_type(&ty);
        assert_eq!(sort, Sort::String);
    }
}

#[test]
fn test_quantifier_sort_opaque_becomes_int() {
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Opaque("String".to_string())),
        Sort::Int
    );
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Opaque("MyStruct".to_string())),
        Sort::Int
    );
}

#[test]
fn test_quantifier_sort_builtin_datatype_becomes_native_carrier() {
    // Native-datatype migration: datatype-bound quantifier variables keep the
    // native carrier sort `Sort::Uninterpreted(name)` (not the legacy `Sort::Int`)
    // so whole-datatype values match ground constructor/selector terms.
    use crate::encoder::datatype::datatype_carrier_sort;
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::from_str("Option<u64>").unwrap()),
        datatype_carrier_sort("Option<u64>")
    );
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::from_str("Result<u32, bool>").unwrap()),
        datatype_carrier_sort("Result<u32, bool>")
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_quantifier_sort_seq_matches_declared_sort() {
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let sort = quantifier_sort_for_type(&seq_ty);
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Seq");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(pointer_width()));
    assert_eq!(arr.element_sort, Sort::bitvec(32));
    assert_eq!(
        sort,
        sort_for_type(&seq_ty),
        "non-native Seq quantifier sort must match declared Seq sort so Seq<T> helper calls encode"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_quantifier_sort_keeps_concrete_element_sort() {
    // #2690: native-seq bound Seq variables must keep the concrete element
    // sort so they match declared function signatures and non-quantifier Seq
    // variables. Only scalar bound variables are widened (Int{32} → Int).
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let declared_sort = sort_for_type(&seq_ty);
    let quantifier_sort = quantifier_sort_for_type(&seq_ty);

    assert_eq!(
        declared_sort,
        Sort::seq(Sort::bitvec(32)),
        "native-seq declared Seq<i32> sort should stay concrete"
    );
    assert_eq!(
        quantifier_sort, declared_sort,
        "native-seq quantifier Seq<i32> must match declared sort to avoid sort mismatch (#2690)"
    );
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Int { width: 32 }),
        Sort::Int,
        "scalar integer sorts still widen to Int in quantifier context"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_quantifier_sort_matches_declared_sort_across_element_types() {
    // #2690: Seq bound variables in quantifiers must keep their concrete
    // element sort to avoid sort mismatches with declared functions.
    let cases = [
        (
            TrustVcType::Int { width: 8 },
            Sort::seq(Sort::bitvec(8)),
            "Seq<i8>",
        ),
        (
            TrustVcType::Int { width: 128 },
            Sort::seq(Sort::bitvec(128)),
            "Seq<i128>",
        ),
        (
            TrustVcType::Uint { width: 8 },
            Sort::seq(Sort::bitvec(8)),
            "Seq<u8>",
        ),
        (
            TrustVcType::Uint { width: 64 },
            Sort::seq(Sort::bitvec(64)),
            "Seq<u64>",
        ),
        (TrustVcType::Char, Sort::seq(Sort::bitvec(32)), "Seq<char>"),
    ];

    for (element_ty, declared_sort, label) in cases {
        let seq_ty = TrustVcType::Seq(Box::new(element_ty));
        assert_eq!(
            sort_for_type(&seq_ty),
            declared_sort,
            "{label} declared sort drifted"
        );
        assert_eq!(
            quantifier_sort_for_type(&seq_ty),
            declared_sort,
            "{label} quantifier sort must match declared sort (#2690)"
        );
    }
}

#[test]
fn test_quantifier_sort_set_uses_element_sort_as_index() {
    let sort =
        quantifier_sort_for_type(&TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Set");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(64));
    assert_eq!(arr.element_sort, Sort::Bool);
}

#[test]
fn test_quantifier_sort_multiset_uses_declared_nat_count_sort() {
    let sort = quantifier_sort_for_type(&TrustVcType::Multiset(Box::new(TrustVcType::Uint {
        width: 64,
    })));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Multiset");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(64));
    assert_eq!(arr.element_sort, Sort::Int);
}

#[test]
fn test_quantifier_sort_map_uses_int_key_and_value() {
    let sort = quantifier_sort_for_type(&TrustVcType::Map(
        Box::new(TrustVcType::Int { width: 32 }),
        Box::new(TrustVcType::Bool),
    ));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Map");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(32));
    assert_eq!(arr.element_sort, Sort::Bool);
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_sort_for_type_nested_collections_use_pointer_width_indices() {
    let sort = sort_for_type(&TrustVcType::from_str("Seq<Seq<i32>>").unwrap());
    let Sort::Array(outer) = &sort else {
        panic!("expected outer Array sort");
    };
    assert_eq!(outer.index_sort, Sort::bitvec(pointer_width()));
    let Sort::Array(inner) = &outer.element_sort else {
        panic!("expected inner Array sort");
    };
    assert_eq!(inner.index_sort, Sort::bitvec(pointer_width()));
    assert_eq!(inner.element_sort, Sort::bitvec(32));
}

#[cfg(feature = "native-seq")]
#[test]
fn test_sort_for_type_nested_seq_uses_native_seq_sort() {
    let sort = sort_for_type(&TrustVcType::from_str("Seq<Seq<i32>>").unwrap());
    assert_eq!(sort, Sort::seq(Sort::seq(Sort::bitvec(32))));
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_sort_for_type_nested_map_value_seq_preserves_value_sort() {
    let sort = sort_for_type(&TrustVcType::from_str("Map<u32, Seq<bool>>").unwrap());
    let Sort::Array(outer) = &sort else {
        panic!("expected outer Array sort");
    };
    assert_eq!(outer.index_sort, Sort::bitvec(32));
    let Sort::Array(inner) = &outer.element_sort else {
        panic!("expected inner Array sort");
    };
    assert_eq!(inner.index_sort, Sort::bitvec(pointer_width()));
    assert_eq!(inner.element_sort, Sort::Bool);
}

#[cfg(feature = "native-seq")]
#[test]
fn test_sort_for_type_nested_map_value_seq_uses_native_seq_sort() {
    let sort = sort_for_type(&TrustVcType::from_str("Map<u32, Seq<bool>>").unwrap());
    let Sort::Array(outer) = &sort else {
        panic!("expected outer Array sort for Map");
    };
    assert_eq!(outer.index_sort, Sort::bitvec(32));
    assert_eq!(outer.element_sort, Sort::seq(Sort::Bool));
}

// === Poly/TypeParam sort mapping (#2053) ===

#[test]
fn test_sort_for_type_type_param_is_poly() {
    assert_eq!(
        sort_for_type(&TrustVcType::TypeParam("T".to_string())),
        Sort::Uninterpreted("Poly".to_string())
    );
    assert_eq!(
        sort_for_type(&TrustVcType::TypeParam("U".to_string())),
        Sort::Uninterpreted("Poly".to_string())
    );
}

#[test]
fn test_sort_for_type_poly_is_poly() {
    assert_eq!(
        sort_for_type(&TrustVcType::Poly),
        Sort::Uninterpreted("Poly".to_string())
    );
}

#[test]
fn test_quantifier_sort_type_param_is_poly() {
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::TypeParam("T".to_string())),
        Sort::Uninterpreted("Poly".to_string())
    );
}

#[test]
fn test_quantifier_sort_poly_is_poly() {
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::Poly),
        Sort::Uninterpreted("Poly".to_string())
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_sort_for_type_seq_of_type_param() {
    let sort = sort_for_type(&TrustVcType::Seq(Box::new(TrustVcType::TypeParam(
        "T".to_string(),
    ))));
    let Sort::Array(arr) = &sort else {
        panic!("expected Array sort for Seq<T>");
    };
    assert_eq!(arr.index_sort, Sort::bitvec(pointer_width()));
    assert_eq!(arr.element_sort, Sort::Uninterpreted("Poly".to_string()));
}

#[cfg(feature = "native-seq")]
#[test]
fn test_sort_for_type_seq_of_type_param_uses_native_seq() {
    let sort = sort_for_type(&TrustVcType::Seq(Box::new(TrustVcType::TypeParam(
        "T".to_string(),
    ))));
    assert_eq!(sort, Sort::seq(Sort::Uninterpreted("Poly".to_string())));
}

#[test]
fn test_sort_for_type_recursive_ref_is_native_carrier() {
    // Native-datatype migration: a `RecursiveRef` resolves to the owning
    // datatype's native carrier sort `Sort::Uninterpreted(name)` (not the legacy
    // shared `Sort::Int`), in both value and quantifier-sort position.
    use crate::encoder::datatype::datatype_carrier_sort;
    assert_eq!(
        sort_for_type(&TrustVcType::RecursiveRef("List_i32".to_string())),
        datatype_carrier_sort("List_i32")
    );
    assert_eq!(
        quantifier_sort_for_type(&TrustVcType::RecursiveRef("List_i32".to_string())),
        datatype_carrier_sort("List_i32")
    );
}
