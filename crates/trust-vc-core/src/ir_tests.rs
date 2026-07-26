// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for TrustVcType (ir.rs). Split out to keep ir.rs under 500 lines.

use super::*;

// === Round-trip: from_str(to_type_string(ty)) == ty ===

#[test]
fn round_trip_canonical_types() {
    let types = [
        TrustVcType::Unit,
        TrustVcType::Bool,
        TrustVcType::Char,
        TrustVcType::StrSlice,
        TrustVcType::String,
        TrustVcType::Int { width: 8 },
        TrustVcType::Int { width: 16 },
        TrustVcType::Int { width: 32 },
        TrustVcType::Int { width: 64 },
        TrustVcType::Int { width: 128 },
        TrustVcType::Uint { width: 8 },
        TrustVcType::Uint { width: 16 },
        TrustVcType::Uint { width: 32 },
        TrustVcType::Uint { width: 64 },
        TrustVcType::Uint { width: 128 },
        TrustVcType::MathInt,
        TrustVcType::Nat,
        TrustVcType::Real,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        TrustVcType::Array(Box::new(TrustVcType::Uint { width: 8 }), 3),
        TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })),
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 16 })),
        TrustVcType::Map(
            Box::new(TrustVcType::Int { width: 32 }),
            Box::new(TrustVcType::Bool),
        ),
        TrustVcType::SpecFn(
            vec![TrustVcType::Int { width: 32 }],
            Box::new(TrustVcType::Bool),
        ),
        TrustVcType::SpecFn(
            vec![
                TrustVcType::Uint {
                    width: pointer_width(),
                },
                TrustVcType::Int { width: 32 },
            ],
            Box::new(TrustVcType::Uint { width: 64 }),
        ),
        TrustVcType::Seq(Box::new(TrustVcType::Char)),
        TrustVcType::from_str("Option<u64>").expect("invariant: test input is valid"),
        TrustVcType::from_str("Result<u32, bool>").expect("invariant: test input is valid"),
        TrustVcType::from_str("List<i32>").expect("invariant: test input is valid"),
        TrustVcType::from_str("Tree<bool>").expect("invariant: test input is valid"),
    ];
    for ty in &types {
        let s = ty.to_type_string();
        let parsed = TrustVcType::from_str(&s).expect("invariant: test input is valid");
        assert_eq!(ty, &parsed, "Round-trip failed for '{}' -> {:?}", s, parsed);
    }
}

#[test]
fn fixed_array_type_parses_and_roundtrips() {
    assert_eq!(
        TrustVcType::from_str("[u8; 3]").expect("fixed array should parse"),
        TrustVcType::Array(Box::new(TrustVcType::Uint { width: 8 }), 3)
    );
    assert_eq!(
        TrustVcType::from_str("[u8;3]").expect("compact fixed array should parse"),
        TrustVcType::Array(Box::new(TrustVcType::Uint { width: 8 }), 3)
    );
    let nested = TrustVcType::from_str("[Seq<i32>; 2]").expect("nested fixed array should parse");
    assert_eq!(
        nested,
        TrustVcType::Array(
            Box::new(TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))),
            2
        )
    );
    assert_eq!(
        TrustVcType::from_str(&nested.to_type_string()).expect("array roundtrip should parse"),
        nested
    );
}

#[test]
fn unsized_slice_type_parses_as_seq_view_carrier() {
    let expected = TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }));
    assert_eq!(
        TrustVcType::from_str("[u8]").expect("unsized slice should parse"),
        expected
    );
    assert_eq!(
        TrustVcType::from_str("&[u8]").expect("borrowed slice should parse"),
        expected
    );
}

// === isize/usize normalization ===

#[test]
fn isize_usize_normalize_to_pointer_width() {
    use crate::ir::pointer_width;

    let isize_ty = TrustVcType::from_str("isize").expect("invariant: test input is valid");
    assert_eq!(
        isize_ty,
        TrustVcType::Int {
            width: pointer_width()
        }
    );

    let usize_ty = TrustVcType::from_str("usize").expect("invariant: test input is valid");
    assert_eq!(
        usize_ty,
        TrustVcType::Uint {
            width: pointer_width()
        }
    );
}

// === f32/f64 parse to distinct Float variants (#2517 Float/Real split) ===

#[test]
fn f32_f64_parse_to_distinct_float_types() {
    let f32_ty = TrustVcType::from_str("f32").expect("invariant: test input is valid");
    let f64_ty = TrustVcType::from_str("f64").expect("invariant: test input is valid");
    // After #2517 Float/Real split, f32 and f64 are distinct Float variants
    assert_eq!(f32_ty, TrustVcType::Float { width: 32 });
    assert_eq!(f64_ty, TrustVcType::Float { width: 64 });
    assert_ne!(f32_ty, f64_ty);
    // to_type_string preserves width
    assert_eq!(f32_ty.to_type_string(), "f32");
    assert_eq!(f64_ty.to_type_string(), "f64");
}

// === contains_float (#1735, updated for Float/Real split #2517) ===

#[test]
fn contains_float_direct() {
    // Float (IEEE 754) stays distinguishable from spec-level `real`.
    assert!(TrustVcType::Float { width: 32 }.contains_float());
    assert!(TrustVcType::Float { width: 64 }.contains_float());
    // Real (spec-level) remains separate and uses SMT Real.
    assert!(!TrustVcType::Real.contains_float());
}

#[test]
fn contains_float_nested_seq() {
    assert!(TrustVcType::Seq(Box::new(TrustVcType::Float { width: 64 })).contains_float());
    // Seq<Real> remains distinct from IEEE floats.
    assert!(!TrustVcType::Seq(Box::new(TrustVcType::Real)).contains_float());
}

#[test]
fn contains_float_false_for_int() {
    assert!(!TrustVcType::Int { width: 32 }.contains_float());
    assert!(!TrustVcType::Bool.contains_float());
    assert!(!TrustVcType::Unit.contains_float());
}

// === Strict from_str rejects unknown types (#2126) ===

#[test]
fn from_str_rejects_unknown_types() {
    let ty = "Widget";
    assert!(
        TrustVcType::from_str(ty).is_err(),
        "strict from_str should reject '{}' (#2126)",
        ty
    );
    assert!(TrustVcType::from_str("").is_err());
    assert!(TrustVcType::from_str("Map<i32>").is_err());
}

#[test]
fn from_str_preserves_legacy_error_messages() {
    assert_eq!(
        TrustVcType::from_str("Widget").unwrap_err(),
        "Unknown type: Widget"
    );
    assert_eq!(
        TrustVcType::from_str("Map<i32>").unwrap_err(),
        "Invalid Map type syntax: Map<i32>"
    );
    assert_eq!(
        TrustVcType::from_str("Result<u64>").unwrap_err(),
        "Invalid Result type syntax: Result<u64>"
    );
    assert_eq!(
        TrustVcType::from_str("SpecFn<u64>").unwrap_err(),
        "Invalid SpecFn type syntax: SpecFn<u64>"
    );
}

#[test]
fn try_from_str_surfaces_trust_vc_error_context() {
    match TrustVcType::try_from_str("Map<i32>") {
        Err(TrustVcTypeParseError::InvalidSyntax { kind, input }) => {
            assert_eq!(kind, "Map");
            assert_eq!(input, "Map<i32>");
        }
        other => panic!(
            "expected structured TrustVcTypeParseError for malformed map type, got: {:?}",
            other
        ),
    }
}

#[test]
fn from_str_parses_builtin_datatypes() {
    let option = TrustVcType::from_str("Option<u64>").expect("Option<u64> should parse");
    assert_eq!(
        option,
        TrustVcType::Datatype {
            name: "Option<u64>".to_string(),
            variants: vec![
                DatatypeVariant {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeVariant {
                    name: "Some".to_string(),
                    fields: vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
                },
            ],
        }
    );

    let result =
        TrustVcType::from_str("Result<u32, bool>").expect("Result<u32, bool> should parse");
    assert_eq!(
        result,
        TrustVcType::Datatype {
            name: "Result<u32, bool>".to_string(),
            variants: vec![
                DatatypeVariant {
                    name: "Ok".to_string(),
                    fields: vec![("0".to_string(), TrustVcType::Uint { width: 32 })],
                },
                DatatypeVariant {
                    name: "Err".to_string(),
                    fields: vec![("0".to_string(), TrustVcType::Bool)],
                },
            ],
        }
    );
}

// === parse_or_opaque for unrecognized types (#1917, #2126) ===

#[test]
fn parse_or_opaque_wraps_unknown_types() {
    let ty = "Widget";
    let parsed = TrustVcType::parse_or_opaque(ty);
    assert_eq!(parsed, TrustVcType::Opaque(ty.to_string()));
    assert_eq!(parsed.to_type_string(), ty);
    assert!(!parsed.is_unsigned() && !parsed.is_collection() && !parsed.is_integer());
    assert_eq!(parsed.bit_width(), None);
}

#[test]
fn vec_types_parse_as_seq_view_surfaces() {
    assert_eq!(
        TrustVcType::from_str("Vec<i32>").expect("Vec<i32> should parse"),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
    assert_eq!(
        TrustVcType::parse_or_opaque("alloc::vec::Vec<u8>"),
        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
    );
}

// === parse_or_opaque succeeds for valid types ===

#[test]
fn parse_or_opaque_parses_valid_types() {
    assert_eq!(TrustVcType::parse_or_opaque("char"), TrustVcType::Char);
    assert_eq!(TrustVcType::parse_or_opaque("str"), TrustVcType::StrSlice);
    assert_eq!(TrustVcType::parse_or_opaque("String"), TrustVcType::String);
    assert_eq!(
        TrustVcType::parse_or_opaque("i32"),
        TrustVcType::Int { width: 32 }
    );
    assert_eq!(TrustVcType::parse_or_opaque("bool"), TrustVcType::Bool);
    assert!(matches!(
        TrustVcType::parse_or_opaque("Seq<u64>"),
        TrustVcType::Seq(_)
    ));
    assert_eq!(
        TrustVcType::parse_or_opaque("Seq<char>"),
        TrustVcType::Seq(Box::new(TrustVcType::Char))
    );
    assert!(matches!(
        TrustVcType::parse_or_opaque("Option<u64>"),
        TrustVcType::Datatype { .. }
    ));
    assert!(matches!(
        TrustVcType::parse_or_opaque("Multiset<u64>"),
        TrustVcType::Multiset(_)
    ));
    assert!(matches!(
        TrustVcType::parse_or_opaque("Result<u64, bool>"),
        TrustVcType::Datatype { .. }
    ));
    assert_eq!(
        TrustVcType::parse_or_opaque("SpecFn<(usize, i32), bool>"),
        TrustVcType::SpecFn(
            vec![
                TrustVcType::Uint {
                    width: pointer_width(),
                },
                TrustVcType::Int { width: 32 },
            ],
            Box::new(TrustVcType::Bool),
        )
    );
}

#[test]
fn parse_or_opaque_keeps_builtin_datatype_shape_with_opaque_fields() {
    let parsed = TrustVcType::parse_or_opaque("Option<Widget>");
    assert_eq!(parsed.to_type_string(), "Option<Widget>");
    assert!(parsed.contains_opaque());

    match parsed {
        TrustVcType::Datatype { name, variants } => {
            assert_eq!(name, "Option<Widget>");
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].name, "None");
            assert_eq!(variants[1].name, "Some");
            assert_eq!(
                variants[1].fields,
                vec![("0".to_string(), TrustVcType::Opaque("Widget".to_string()))]
            );
        }
        other => panic!("expected built-in datatype, got: {:?}", other),
    }
}

// === bit_width (#1950) ===

#[test]
fn bit_width_returns_none_for_non_bv_types() {
    // #1950: bit_width() previously returned Some(0) for Bool and MathInt,
    // causing bvextract(inner, u32::MAX, 0) underflow in cast paths.
    assert_eq!(TrustVcType::Bool.bit_width(), None);
    assert_eq!(TrustVcType::MathInt.bit_width(), None);
    assert_eq!(TrustVcType::Nat.bit_width(), None);
    assert_eq!(TrustVcType::Real.bit_width(), None);
    assert_eq!(TrustVcType::Opaque("Widget".to_string()).bit_width(), None);
    assert_eq!(
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })).bit_width(),
        None
    );
    assert_eq!(
        TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })).bit_width(),
        None
    );
    assert_eq!(
        TrustVcType::Map(
            Box::new(TrustVcType::Int { width: 32 }),
            Box::new(TrustVcType::Bool),
        )
        .bit_width(),
        None
    );
}

#[test]
fn bit_width_returns_width_for_integer_types() {
    assert_eq!(TrustVcType::Char.bit_width(), Some(32));
    assert_eq!(TrustVcType::Int { width: 8 }.bit_width(), Some(8));
    assert_eq!(TrustVcType::Int { width: 32 }.bit_width(), Some(32));
    assert_eq!(TrustVcType::Uint { width: 64 }.bit_width(), Some(64));
    assert_eq!(TrustVcType::Uint { width: 128 }.bit_width(), Some(128));
}

#[test]
fn contains_opaque_detects_nested_variants() {
    assert!(TrustVcType::Opaque("Widget".to_string()).contains_opaque());
    assert!(
        TrustVcType::Seq(Box::new(TrustVcType::Opaque("Widget".to_string()))).contains_opaque()
    );
    assert!(
        TrustVcType::Array(Box::new(TrustVcType::Opaque("Widget".to_string())), 2)
            .contains_opaque()
    );
    assert!(TrustVcType::Map(
        Box::new(TrustVcType::Uint { width: 32 }),
        Box::new(TrustVcType::Opaque("Vec<bool>".to_string())),
    )
    .contains_opaque());
    assert!(
        TrustVcType::Multiset(Box::new(TrustVcType::Opaque("Widget".to_string())))
            .contains_opaque()
    );
    assert!(TrustVcType::parse_or_opaque("Option<Widget>").contains_opaque());
    assert!(!TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 })).contains_opaque());
    assert!(!TrustVcType::String.contains_opaque());
    assert!(!TrustVcType::Seq(Box::new(TrustVcType::Char)).contains_opaque());
}

#[test]
fn collection_elem_returns_inner_value_types() {
    assert_eq!(
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })).collection_elem(),
        Some(TrustVcType::Int { width: 32 })
    );
    assert_eq!(
        TrustVcType::Array(Box::new(TrustVcType::Uint { width: 8 }), 3).collection_elem(),
        Some(TrustVcType::Uint { width: 8 })
    );
    assert_eq!(
        TrustVcType::Set(Box::new(TrustVcType::Uint { width: 64 })).collection_elem(),
        Some(TrustVcType::Uint { width: 64 })
    );
    assert_eq!(
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 16 })).collection_elem(),
        Some(TrustVcType::Int { width: 16 })
    );
    assert_eq!(
        TrustVcType::Map(
            Box::new(TrustVcType::Int { width: 32 }),
            Box::new(TrustVcType::Bool),
        )
        .collection_elem(),
        Some(TrustVcType::Bool)
    );
    assert_eq!(TrustVcType::Bool.collection_elem(), None);
    assert_eq!(TrustVcType::String.collection_elem(), None);
    assert_eq!(TrustVcType::StrSlice.collection_elem(), None);
}

#[test]
fn string_like_view_collection_type_exposes_seq_char_only_via_view() {
    assert_eq!(
        TrustVcType::String.view_collection_type(),
        Some(TrustVcType::Seq(Box::new(TrustVcType::Char)))
    );
    assert_eq!(
        TrustVcType::StrSlice.view_collection_type(),
        Some(TrustVcType::Seq(Box::new(TrustVcType::Char)))
    );
    assert_eq!(
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })).view_collection_type(),
        Some(TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })))
    );
    assert_eq!(
        TrustVcType::Array(Box::new(TrustVcType::Uint { width: 8 }), 3).view_collection_type(),
        Some(TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 })))
    );
    assert_eq!(
        TrustVcType::Multiset(Box::new(TrustVcType::Bool)).view_collection_type(),
        Some(TrustVcType::Multiset(Box::new(TrustVcType::Bool)))
    );
    assert!(!TrustVcType::String.is_collection());
    assert!(TrustVcType::String.is_string_like());
    assert!(TrustVcType::String.has_collection_length());
    assert!(!TrustVcType::Char.has_collection_length());
}

#[test]
fn multiset_parses_and_round_trips() {
    let multiset = TrustVcType::from_str("Multiset<i32>").expect("Multiset<i32> should parse");
    assert_eq!(
        multiset,
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
    );
    assert!(multiset.is_collection());
    assert_eq!(multiset.to_type_string(), "Multiset<i32>");
}

#[test]
fn recursive_ref_preserves_name_without_inlining() {
    let recursive = TrustVcType::RecursiveRef("List_i32".to_string());
    assert_eq!(recursive.to_type_string(), "List_i32");
    assert!(!recursive.contains_opaque());
    assert!(!recursive.contains_float());
    assert!(!recursive.is_collection());
    assert_eq!(recursive.collection_elem(), None);
}

// === TypeParam and Poly variants (#2053) ===

#[test]
fn type_param_to_type_string() {
    assert_eq!(
        TrustVcType::TypeParam("T".to_string()).to_type_string(),
        "T"
    );
    assert_eq!(
        TrustVcType::TypeParam("U".to_string()).to_type_string(),
        "U"
    );
}

#[test]
fn poly_to_type_string() {
    assert_eq!(TrustVcType::Poly.to_type_string(), "Poly");
}

#[test]
fn type_param_is_not_opaque() {
    assert!(!TrustVcType::TypeParam("T".to_string()).contains_opaque());
    assert!(!TrustVcType::Poly.contains_opaque());
}

// === Nat type (#2418) ===

#[test]
fn nat_parse_and_roundtrip() {
    let nat = TrustVcType::from_str("nat").expect("nat should parse");
    assert_eq!(nat, TrustVcType::Nat);
    assert_eq!(nat.to_type_string(), "nat");
    let rt = TrustVcType::from_str(&nat.to_type_string()).expect("round-trip should parse");
    assert_eq!(rt, TrustVcType::Nat);
}

#[test]
fn nat_is_not_integer_or_unsigned() {
    // Nat is unbounded (Sort::Int), not a bitvector type.
    assert!(!TrustVcType::Nat.is_integer());
    assert!(!TrustVcType::Nat.is_unsigned());
    assert!(!TrustVcType::Nat.is_collection());
    assert!(!TrustVcType::Nat.contains_opaque());
}

#[test]
fn nat_distinct_from_math_int() {
    // Nat and MathInt are semantically different (Nat has non-negativity).
    assert_ne!(TrustVcType::Nat, TrustVcType::MathInt);
    assert_eq!(TrustVcType::from_str("nat").unwrap(), TrustVcType::Nat);
    assert_eq!(TrustVcType::from_str("int").unwrap(), TrustVcType::MathInt);
}

#[test]
fn type_param_is_not_integer() {
    assert!(!TrustVcType::TypeParam("T".to_string()).is_integer());
    assert!(!TrustVcType::Poly.is_integer());
}

#[test]
fn type_param_has_no_bit_width() {
    assert_eq!(TrustVcType::TypeParam("T".to_string()).bit_width(), None);
    assert_eq!(TrustVcType::Poly.bit_width(), None);
}

#[test]
fn type_param_is_not_collection() {
    assert!(!TrustVcType::TypeParam("T".to_string()).is_collection());
    assert!(!TrustVcType::Poly.is_collection());
}

#[test]
fn type_param_is_not_unsigned() {
    assert!(!TrustVcType::TypeParam("T".to_string()).is_unsigned());
    assert!(!TrustVcType::Poly.is_unsigned());
}

#[test]
fn type_param_collection_elem_is_none() {
    assert_eq!(
        TrustVcType::TypeParam("T".to_string()).collection_elem(),
        None
    );
    assert_eq!(TrustVcType::Poly.collection_elem(), None);
}

#[test]
fn type_param_equality_and_hash() {
    use std::collections::HashSet;
    let t1 = TrustVcType::TypeParam("T".to_string());
    let t2 = TrustVcType::TypeParam("T".to_string());
    let u = TrustVcType::TypeParam("U".to_string());
    assert_eq!(t1, t2);
    assert_ne!(t1, u);
    assert_ne!(t1, TrustVcType::Poly);

    let mut set = HashSet::new();
    set.insert(t1.clone());
    set.insert(t2);
    set.insert(TrustVcType::Poly);
    assert_eq!(set.len(), 2); // T (deduped) + Poly
}

#[test]
fn seq_of_type_param_is_not_opaque() {
    let seq_t = TrustVcType::Seq(Box::new(TrustVcType::TypeParam("T".to_string())));
    assert!(!seq_t.contains_opaque());
    assert!(seq_t.is_collection());
    assert_eq!(
        seq_t.collection_elem(),
        Some(TrustVcType::TypeParam("T".to_string()))
    );
}

// === Ghost/Tracked/Proph wrapper erasure (Part of #2427, #2519) ===

#[test]
fn tracked_u32_erases_to_uint32() {
    let parsed = TrustVcType::parse_or_opaque("Tracked<u32>");
    assert_eq!(parsed, TrustVcType::Uint { width: 32 });
}

#[test]
fn tracked_i64_erases_to_int64() {
    let parsed = TrustVcType::parse_or_opaque("Tracked<i64>");
    assert_eq!(parsed, TrustVcType::Int { width: 64 });
}

#[test]
fn ghost_bool_erases_to_bool() {
    let parsed = TrustVcType::parse_or_opaque("Ghost<bool>");
    assert_eq!(parsed, TrustVcType::Bool);
}

#[test]
fn ghost_seq_erases_to_seq() {
    let parsed = TrustVcType::parse_or_opaque("Ghost<Seq<i32>>");
    assert_eq!(
        parsed,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
fn tracked_seq_erases_to_seq() {
    let parsed = TrustVcType::parse_or_opaque("Tracked<Seq<u64>>");
    assert_eq!(
        parsed,
        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 64 }))
    );
}

#[test]
fn strict_tracked_parse_succeeds() {
    let result =
        TrustVcType::try_from_str("Tracked<u32>").expect("Tracked<u32> should parse successfully");
    assert_eq!(result, TrustVcType::Uint { width: 32 });
}

#[test]
fn strict_ghost_parse_succeeds() {
    let result =
        TrustVcType::try_from_str("Ghost<bool>").expect("Ghost<bool> should parse successfully");
    assert_eq!(result, TrustVcType::Bool);
}

#[test]
fn proph_u32_erases_to_uint32() {
    let parsed = TrustVcType::parse_or_opaque("Proph<u32>");
    assert_eq!(parsed, TrustVcType::Uint { width: 32 });
}

#[test]
fn strict_proph_parse_succeeds() {
    let result = TrustVcType::try_from_str("Proph<Seq<u64>>")
        .expect("Proph<Seq<u64>> should parse successfully");
    assert_eq!(
        result,
        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 64 }))
    );
}

// === Snapshot<T> wrapper erasure ===

#[test]
fn snapshot_u32_erases_to_uint32() {
    let parsed = TrustVcType::parse_or_opaque("Snapshot<u32>");
    assert_eq!(parsed, TrustVcType::Uint { width: 32 });
}

#[test]
fn snapshot_seq_erases_to_seq() {
    let parsed = TrustVcType::parse_or_opaque("Snapshot<Seq<i32>>");
    assert_eq!(
        parsed,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
fn strict_snapshot_parse_succeeds() {
    let result = TrustVcType::try_from_str("Snapshot<bool>")
        .expect("Snapshot<bool> should parse successfully");
    assert_eq!(result, TrustVcType::Bool);
}

// === List<T> recursive datatype parsing (#2421 Slice 5) ===

#[test]
fn list_i32_parses_to_recursive_datatype() {
    let ty = TrustVcType::from_str("List<i32>").expect("List<i32> should parse");
    let TrustVcType::Datatype { name, variants } = &ty else {
        panic!("List<i32> should parse to Datatype, got {:?}", ty);
    };
    assert_eq!(name, "List<i32>");
    assert_eq!(variants.len(), 2);

    let nil = &variants[0];
    assert_eq!(nil.name, "Nil");
    assert!(nil.fields.is_empty());

    let cons = &variants[1];
    assert_eq!(cons.name, "Cons");
    assert_eq!(cons.fields.len(), 2);
    assert_eq!(cons.fields[0].0, "head");
    assert_eq!(cons.fields[0].1, TrustVcType::Int { width: 32 });
    assert_eq!(cons.fields[1].0, "tail");
    assert_eq!(
        cons.fields[1].1,
        TrustVcType::RecursiveRef("List<i32>".to_string())
    );
}

#[test]
fn list_u64_roundtrips_through_type_string() {
    let ty = TrustVcType::from_str("List<u64>").expect("List<u64> should parse");
    assert_eq!(ty.to_type_string(), "List<u64>");
}

#[test]
fn list_is_collection_type() {
    let ty = TrustVcType::from_str("List<i32>").expect("List<i32> should parse");
    // List is a Datatype, not a collection (Seq/Set/Map/Multiset).
    // It should NOT match is_collection().
    assert!(!ty.is_collection());
}

// === Tree<T> recursive datatype parsing (#2421 Slice 5) ===

#[test]
fn tree_i32_parses_to_recursive_datatype() {
    let ty = TrustVcType::from_str("Tree<i32>").expect("Tree<i32> should parse");
    let TrustVcType::Datatype { name, variants } = &ty else {
        panic!("Tree<i32> should parse to Datatype, got {:?}", ty);
    };
    assert_eq!(name, "Tree<i32>");
    assert_eq!(variants.len(), 2);

    let leaf = &variants[0];
    assert_eq!(leaf.name, "Leaf");
    assert_eq!(leaf.fields.len(), 1);
    assert_eq!(leaf.fields[0].0, "val");
    assert_eq!(leaf.fields[0].1, TrustVcType::Int { width: 32 });

    let branch = &variants[1];
    assert_eq!(branch.name, "Branch");
    assert_eq!(branch.fields.len(), 2);
    assert_eq!(branch.fields[0].0, "left");
    assert_eq!(
        branch.fields[0].1,
        TrustVcType::RecursiveRef("Tree<i32>".to_string())
    );
    assert_eq!(branch.fields[1].0, "right");
    assert_eq!(
        branch.fields[1].1,
        TrustVcType::RecursiveRef("Tree<i32>".to_string())
    );
}

#[test]
fn tree_bool_roundtrips_through_type_string() {
    let ty = TrustVcType::from_str("Tree<bool>").expect("Tree<bool> should parse");
    assert_eq!(ty.to_type_string(), "Tree<bool>");
}

#[test]
fn list_and_tree_register_as_recursive_datatypes() {
    // Verify that List and Tree parsed types trigger well-foundedness
    // axioms when registered (they have RecursiveRef fields).
    let list = TrustVcType::from_str("List<i32>").expect("parse");
    let tree = TrustVcType::from_str("Tree<u64>").expect("parse");

    let TrustVcType::Datatype {
        variants: list_v, ..
    } = &list
    else {
        panic!()
    };
    let TrustVcType::Datatype {
        variants: tree_v, ..
    } = &tree
    else {
        panic!()
    };

    // List Cons has a RecursiveRef field
    let cons = &list_v[1];
    assert!(cons
        .fields
        .iter()
        .any(|(_, ty)| matches!(ty, TrustVcType::RecursiveRef(_))));

    // Tree Branch has two RecursiveRef fields
    let branch = &tree_v[1];
    let recursive_count = branch
        .fields
        .iter()
        .filter(|(_, ty)| matches!(ty, TrustVcType::RecursiveRef(_)))
        .count();
    assert_eq!(recursive_count, 2);
}

#[test]
fn list_well_foundedness_accepts_nil_base_case() {
    let ty = TrustVcType::from_str("List<i32>").expect("List<i32> should parse");
    ty.validate_well_foundedness()
        .expect("List should be accepted as well-founded");
}

#[test]
fn option_well_foundedness_accepts_non_recursive_datatype() {
    let ty = TrustVcType::from_str("Option<u64>").expect("Option<u64> should parse");
    ty.validate_well_foundedness()
        .expect("non-recursive datatypes should be trivially well-founded");
}

#[test]
fn well_foundedness_rejects_recursive_datatype_without_base_case() {
    let ty = TrustVcType::Datatype {
        name: "Bad".to_string(),
        variants: vec![
            DatatypeVariant::new(
                "Node",
                vec![(
                    "next".to_string(),
                    TrustVcType::RecursiveRef("Bad".to_string()),
                )],
            ),
            DatatypeVariant::new(
                "Alias",
                vec![(
                    "rest".to_string(),
                    TrustVcType::RecursiveRef("Bad".to_string()),
                )],
            ),
        ],
    };

    let err = ty
        .validate_well_foundedness()
        .expect_err("recursive datatype without a base case must be rejected");
    assert!(
        err.contains("Recursive cycle in datatype 'Bad' has no base case variant"),
        "expected base-case diagnostic, got: {err}"
    );
    assert!(
        err.contains("Box<T>, Arc<T>, or Rc<T>"),
        "expected indirection guidance, got: {err}"
    );
}

#[test]
fn try_validate_well_foundedness_surfaces_typed_base_case_error() {
    let ty = TrustVcType::Datatype {
        name: "Bad".to_string(),
        variants: vec![DatatypeVariant::new(
            "Node",
            vec![(
                "next".to_string(),
                TrustVcType::RecursiveRef("Bad".to_string()),
            )],
        )],
    };

    match ty.try_validate_well_foundedness() {
        Err(DatatypeWellFoundednessError::NoBaseCase { datatype }) => {
            assert_eq!(datatype, "Bad");
        }
        other => panic!("expected typed DatatypeWellFoundednessError::NoBaseCase, got: {other:?}"),
    }
}

#[test]
fn tree_well_foundedness_accepts_leaf_base_case() {
    let ty = TrustVcType::from_str("Tree<bool>").expect("Tree<bool> should parse");
    ty.validate_well_foundedness()
        .expect("Tree should be accepted as well-founded");
}

#[test]
fn well_foundedness_rejects_cross_datatype_recursive_cycle() {
    let left = TrustVcType::Datatype {
        name: "Left".to_string(),
        variants: vec![DatatypeVariant::new(
            "LeftNode",
            vec![(
                "right".to_string(),
                TrustVcType::RecursiveRef("Right".to_string()),
            )],
        )],
    };
    let right = TrustVcType::Datatype {
        name: "Right".to_string(),
        variants: vec![DatatypeVariant::new(
            "RightNode",
            vec![(
                "left".to_string(),
                TrustVcType::RecursiveRef("Left".to_string()),
            )],
        )],
    };

    for (name, ty, target) in [("Left", left, "Right"), ("Right", right, "Left")] {
        let err = ty
            .validate_well_foundedness()
            .expect_err("cross-datatype recursion must fail closed");
        assert!(
            err.contains(&format!(
                "Recursive datatype '{name}' references other datatype carriers ({target})"
            )),
            "expected referenced carrier in diagnostic, got: {err}"
        );
        assert!(
            err.contains("Mutual recursive datatype cycles are not supported yet"),
            "expected unsupported-cycle diagnostic, got: {err}"
        );
    }
}

#[test]
fn try_validate_well_foundedness_surfaces_typed_mutual_recursion_targets() {
    let ty = TrustVcType::Datatype {
        name: "Left".to_string(),
        variants: vec![DatatypeVariant::new(
            "LeftNode",
            vec![(
                "right".to_string(),
                TrustVcType::RecursiveRef("Right".to_string()),
            )],
        )],
    };

    match ty.try_validate_well_foundedness() {
        Err(DatatypeWellFoundednessError::MutualRecursionUnsupported {
            datatype,
            targets,
        }) => {
            assert_eq!(datatype, "Left");
            assert_eq!(targets, "Right");
        }
        other => panic!(
            "expected typed DatatypeWellFoundednessError::MutualRecursionUnsupported, got: {other:?}"
        ),
    }
}

// === `global size_of usize == N` architecture directive (#2778) ===

#[test]
fn parse_global_size_of_usize_recognizes_4_and_8_bytes() {
    assert_eq!(
        parse_global_size_of_usize("global size_of usize == 4;"),
        Some(Ok(32)),
        "size 4 bytes => 32-bit usize"
    );
    assert_eq!(
        parse_global_size_of_usize("global size_of usize == 8;"),
        Some(Ok(64)),
        "size 8 bytes => 64-bit usize"
    );
    assert_eq!(
        parse_global_size_of_usize("global size_of usize == 2"),
        Some(Ok(16)),
        "size 2 bytes => 16-bit usize, trailing semicolon optional"
    );
}

#[test]
fn parse_global_size_of_usize_tolerates_whitespace() {
    assert_eq!(
        parse_global_size_of_usize("   global   size_of   usize   ==   8  ;  "),
        Some(Ok(64))
    );
}

#[test]
fn parse_global_size_of_usize_rejects_unsupported_width_fail_closed() {
    // 5 bytes => 40 bits, which Rust never uses for usize. Must surface an
    // error rather than silently accepting an unrealizable target.
    let result = parse_global_size_of_usize("global size_of usize == 5;");
    assert!(
        matches!(result, Some(Err(_))),
        "unsupported byte size must fail closed, got {result:?}"
    );
    // 16 bytes => 128 bits is also not a valid usize width.
    assert!(matches!(
        parse_global_size_of_usize("global size_of usize == 16;"),
        Some(Err(_))
    ));
    // Non-numeric RHS is recognized as the directive but invalid.
    assert!(matches!(
        parse_global_size_of_usize("global size_of usize == foo;"),
        Some(Err(_))
    ));
}

#[test]
fn parse_global_size_of_usize_ignores_unrelated_lines() {
    assert_eq!(parse_global_size_of_usize("let x: usize = 0;"), None);
    assert_eq!(parse_global_size_of_usize("global size_of u32 == 4;"), None);
    assert_eq!(
        parse_global_size_of_usize("global size_of usize_t == 4;"),
        None,
        "`usize_t` is not the `usize` token"
    );
    assert_eq!(
        parse_global_size_of_usize("globalsize_of usize == 4;"),
        None,
        "`global` must be a standalone token"
    );
    assert_eq!(parse_global_size_of_usize("// a comment"), None);
}

#[test]
fn pointer_width_guard_overrides_and_restores() {
    let host = usize::BITS;
    assert_eq!(pointer_width(), host, "no override by default");
    {
        let _g = PointerWidthGuard::install(32);
        assert_eq!(pointer_width(), 32);
        // usize/isize parse to the overridden width while the guard is live.
        assert_eq!(TrustVcType::parse_or_opaque("usize").bit_width(), Some(32));
        assert_eq!(TrustVcType::parse_or_opaque("isize").bit_width(), Some(32));
        {
            let _g2 = PointerWidthGuard::install(64);
            assert_eq!(pointer_width(), 64, "nested override applies");
        }
        assert_eq!(pointer_width(), 32, "nested guard restores outer override");
    }
    assert_eq!(pointer_width(), host, "guard restores host width on drop");
}

#[test]
fn scan_pointer_width_directive_installs_from_source() {
    let src = "global size_of usize == 4;\nfn f() { let x: usize = 0; }";
    let guard = scan_pointer_width_directive(src).expect("valid directive");
    assert!(guard.is_some(), "directive should install a guard");
    let _guard = guard;
    assert_eq!(pointer_width(), 32);
}

#[test]
fn scan_pointer_width_directive_none_when_absent() {
    let src = "fn f() { let x: usize = 0; }";
    let guard = scan_pointer_width_directive(src).expect("no error");
    assert!(guard.is_none());
    assert_eq!(pointer_width(), usize::BITS, "host width unchanged");
}

#[test]
fn pinned_width_from_guard_reads_width_and_releases_override() {
    // A scanned directive installs its width; pinned_width_from_guard reads it
    // and then drops the guard, restoring the host width (clean state for callers
    // that re-install per pass).
    let host = pointer_width();
    let src = "global size_of usize == 4;\nfn f() {}";
    let guard = scan_pointer_width_directive(src).expect("valid directive");
    assert_eq!(
        pinned_width_from_guard(guard),
        Some(32),
        "the pinned width must be reported"
    );
    assert_eq!(
        pointer_width(),
        host,
        "the guard must be released after reading, restoring the host width"
    );
}

#[test]
fn pinned_width_from_guard_none_when_no_directive() {
    let host = pointer_width();
    let guard = scan_pointer_width_directive("fn f() {}").expect("no error");
    assert_eq!(pinned_width_from_guard(guard), None);
    assert_eq!(
        pointer_width(),
        host,
        "host width unchanged when no directive"
    );
}

#[test]
fn scan_pointer_width_directive_rejects_conflicts() {
    let src = "global size_of usize == 4;\nglobal size_of usize == 8;";
    assert!(
        scan_pointer_width_directive(src).is_err(),
        "conflicting widths must be rejected"
    );
    // Identical repeated directives are fine.
    let ok = "global size_of usize == 8;\nglobal size_of usize == 8;";
    assert!(scan_pointer_width_directive(ok).is_ok());
}

#[test]
fn strip_pointer_width_directives_blanks_valid_lines_and_keeps_layout() {
    let src = "global size_of usize == 4;\nfn f() { let x: usize = 0; }\n";
    let stripped = strip_pointer_width_directives(src);
    // The directive line is removed (blanked) but the line count is preserved so
    // diagnostics line numbers stay accurate, and the body survives verbatim.
    assert_eq!(stripped, "\nfn f() { let x: usize = 0; }\n");
    // The surviving code must parse as a Rust file (the raw directive would not).
    assert!(syn::parse_file(&stripped).is_ok());
}

#[test]
fn strip_pointer_width_directives_noop_without_directive() {
    let src = "fn f() { let x: usize = 0; }\n";
    assert_eq!(strip_pointer_width_directives(src), src);
}

#[test]
fn strip_pointer_width_directives_preserves_malformed_lines() {
    // A malformed directive is left in place so `scan_pointer_width_directive`
    // can report it; stripping it would mask the error.
    let src = "global size_of usize == 5;\nfn f() {}\n";
    assert_eq!(strip_pointer_width_directives(src), src);
}

#[test]
fn strip_pointer_width_directives_without_trailing_newline() {
    let src = "global size_of usize == 8;\nfn f() {}";
    assert_eq!(strip_pointer_width_directives(src), "\nfn f() {}");
}

// === generic recursive datatype monomorphization (per-instantiation carrier) ===

/// The TEMPLATE carrier for `GList<T>`: `GCons(head: TypeParam("T"),
/// tail: RecursiveRef("GList"))`, base case `GNil`.
fn glist_template() -> TrustVcType {
    TrustVcType::Datatype {
        name: "GList".to_string(),
        variants: vec![
            DatatypeVariant::new("GNil", vec![]),
            DatatypeVariant::new(
                "GCons",
                vec![
                    ("0".to_string(), TrustVcType::TypeParam("T".to_string())),
                    (
                        "1".to_string(),
                        TrustVcType::RecursiveRef("GList".to_string()),
                    ),
                ],
            ),
        ],
    }
}

#[test]
fn monomorphize_renames_carrier_and_self_recursive_ref() {
    let bindings = vec![("T".to_string(), TrustVcType::Int { width: 32 })];
    let mono = glist_template().monomorphize(&bindings);
    let TrustVcType::Datatype { name, variants } = &mono else {
        panic!("expected a datatype carrier, got {mono:?}");
    };
    // Carrier renamed to the per-instantiation name.
    assert_eq!(name, "GList<i32>");
    let gcons = variants.iter().find(|v| v.name == "GCons").unwrap();
    // The generic head field became the concrete element sort.
    assert_eq!(gcons.fields[0].1, TrustVcType::Int { width: 32 });
    // SOUNDNESS: the self-recursion edge is retargeted to THIS carrier — a
    // self-only `RecursiveRef`, never a cross-carrier edge to the bare template.
    assert_eq!(
        gcons.fields[1].1,
        TrustVcType::RecursiveRef("GList<i32>".to_string())
    );
    // The monomorphized carrier is well-founded (self-recursion + base case),
    // NOT a (false) mutual-recursion cycle.
    assert!(mono.try_validate_well_foundedness().is_ok());
}

#[test]
fn monomorphize_keeps_distinct_instantiations_distinct() {
    let as_i32 =
        glist_template().monomorphize(&[("T".to_string(), TrustVcType::Int { width: 32 })]);
    let as_bool = glist_template().monomorphize(&[("T".to_string(), TrustVcType::Bool)]);
    // Distinct instantiations are DISTINCT carriers (never collapsed).
    assert_eq!(as_i32.to_type_string(), "GList<i32>");
    assert_eq!(as_bool.to_type_string(), "GList<bool>");
    assert_ne!(as_i32, as_bool);
}

#[test]
fn monomorphize_with_empty_bindings_is_identity() {
    // A concrete builtin carrier (`List<i32>`) must be preserved verbatim — never
    // stripped to a bare `List` (which would split it from its `RecursiveRef`).
    let concrete = TrustVcType::parse_or_opaque("List<i32>");
    assert_eq!(concrete.monomorphize(&[]), concrete);
}

#[test]
fn collect_type_param_bindings_recovers_element_type() {
    let concrete =
        glist_template().monomorphize(&[("T".to_string(), TrustVcType::Int { width: 32 })]);
    let mut bindings = Vec::new();
    glist_template().collect_type_param_bindings(&concrete, &mut bindings);
    assert_eq!(
        bindings,
        vec![("T".to_string(), TrustVcType::Int { width: 32 })]
    );
}
