//! Type-to-sort mapping, split_generic_args, and type_to_bit_width tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::types::sort_for_type;

// ========================================================================
// Spec collection sort tests (Issue #50)
// ========================================================================

#[test]
#[cfg(not(feature = "native-seq"))]
fn test_type_to_sort_seq() {
    let sort = sort_for_type(&crate::ir::TrustVcType::from_str("Seq<i32>").unwrap());
    // Seq<i32> -> (Array BitVec(64) BitVec(32))
    match sort {
        Sort::Array(arr) => {
            assert_eq!(
                arr.index_sort.bitvec_width(),
                Some(64),
                "Seq index should be BitVec(64) for usize"
            );
            assert!(
                matches!(arr.element_sort, Sort::BitVec(_)),
                "Seq<i32> element should be BitVec"
            );
        }
        _ => panic!("expected Array sort"),
    }
}

#[test]
fn test_type_to_sort_set() {
    let sort = sort_for_type(&crate::ir::TrustVcType::from_str("Set<i64>").unwrap());
    // Set<i64> -> (Array BitVec(64) Bool)
    match sort {
        Sort::Array(arr) => {
            assert!(
                matches!(arr.index_sort, Sort::BitVec(_)),
                "Set<i64> index should be BitVec"
            );
            assert!(
                matches!(arr.element_sort, Sort::Bool),
                "Set element should be Bool"
            );
        }
        _ => panic!("expected Array sort"),
    }
}

#[test]
fn test_type_to_sort_map() {
    let sort = sort_for_type(&crate::ir::TrustVcType::from_str("Map<i32, bool>").unwrap());
    // Map<i32, bool> -> (Array BitVec(32) Bool)
    match sort {
        Sort::Array(arr) => {
            assert!(
                matches!(arr.index_sort, Sort::BitVec(_)),
                "Map<i32, bool> key should be BitVec"
            );
            assert!(
                matches!(arr.element_sort, Sort::Bool),
                "Map<i32, bool> value should be Bool"
            );
        }
        _ => panic!("expected Array sort"),
    }
}

#[test]
#[cfg(not(feature = "native-seq"))]
fn test_type_to_sort_nested_seq() {
    let sort = sort_for_type(&crate::ir::TrustVcType::from_str("Seq<Seq<i32>>").unwrap());
    // Seq<Seq<i32>> -> (Array BitVec(64) (Array BitVec(64) BitVec(32)))
    match sort {
        Sort::Array(arr) => {
            assert_eq!(
                arr.index_sort.bitvec_width(),
                Some(64),
                "Seq index should be BitVec(64) for usize"
            );
            assert!(
                matches!(arr.element_sort, Sort::Array(_)),
                "inner should be Array"
            );
        }
        _ => panic!("expected Array sort"),
    }
}

#[test]
#[cfg(not(feature = "native-seq"))]
fn test_type_to_sort_map_with_seq_value() {
    let sort = sort_for_type(&crate::ir::TrustVcType::from_str("Map<i32, Seq<bool>>").unwrap());
    // Map<i32, Seq<bool>> -> (Array BitVec(32) (Array BitVec(64) Bool))
    match sort {
        Sort::Array(arr) => {
            assert!(
                matches!(arr.index_sort, Sort::BitVec(_)),
                "Map<i32, _> key should be BitVec(32)"
            );
            match arr.element_sort {
                Sort::Array(inner) => {
                    assert_eq!(
                        inner.index_sort.bitvec_width(),
                        Some(64),
                        "Seq index should be BitVec(64) for usize"
                    );
                    assert!(
                        matches!(inner.element_sort, Sort::Bool),
                        "Seq<bool> element should be Bool"
                    );
                }
                _ => panic!("Map value Seq<bool> should be Array sort"),
            }
        }
        _ => panic!("expected Array sort"),
    }
}

#[test]
fn test_split_generic_args() {
    use crate::type_syntax::split_generic_args;

    assert_eq!(split_generic_args("i32, bool"), Some(("i32", " bool")));
    assert_eq!(
        split_generic_args("Map<A, B>, C"),
        Some(("Map<A, B>", " C"))
    );
    assert_eq!(split_generic_args("i32"), None);
}
