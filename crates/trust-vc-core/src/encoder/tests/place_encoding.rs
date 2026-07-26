//! Encoder-level tests for ReadPlace and PlaceDisjoint ay encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests the encoding paths in `ir_encoder/place_encoding.rs`:
//! - `encode_read_place`: converts TrustVcPlace → TrustVcExpr chain → ay Term
//! - `encode_place_disjoint`: delegates to `place_disjoint()` → TrustVcExpr → ay Term
//!
//! Part of #2515 Slice 4.

use super::*;
use crate::ir::{CompareOp, DatatypeVariant, TrustVcExpr, TrustVcType};
use crate::ir_place::TrustVcPlace;
use crate::vc::VariableDecl;

fn i32_dt() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn seq_i32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(i32_dt()))
}

fn counter_variants() -> Vec<DatatypeVariant> {
    vec![DatatypeVariant::new(
        "Counter",
        vec![
            ("count".to_string(), i32_dt()),
            ("max".to_string(), i32_dt()),
        ],
    )]
}

fn counter_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: counter_variants(),
    }
}

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_dt(),
    }
}

// ========================================================================
// PlaceDisjoint encoding
// ========================================================================

/// Different roots → place_disjoint returns BoolLit(true) → assertion verified.
#[test]
fn test_place_disjoint_different_roots_verified() {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_dt(),
        })
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: i32_dt(),
        })
        .unwrap();

    let left = TrustVcPlace::root("x", i32_dt());
    let right = TrustVcPlace::root("y", i32_dt());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };

    let term = encoder.encode_condition_typed(&expr).unwrap();
    let negated = encoder.solver.try_not(term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "different roots must be disjoint (BoolLit(true)), negation should be unsat, got {:?}",
        result
    );
}

/// Same place → place_disjoint returns BoolLit(false) → assertion is SAT (not disjoint).
#[test]
fn test_place_disjoint_same_place_not_disjoint() {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_dt(),
        })
        .unwrap();

    let left = TrustVcPlace::root("x", i32_dt());
    let right = TrustVcPlace::root("x", i32_dt());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };

    let term = encoder.encode_condition_typed(&expr).unwrap();
    // Assert disjoint(x, x) — should be SAT-false, meaning the assertion is false
    encoder.solver.try_assert_term(term).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "same place must NOT be disjoint (BoolLit(false)), asserting false should be unsat, got {:?}",
        result
    );
}

/// Different fields on same root → place_disjoint returns BoolLit(true).
#[test]
fn test_place_disjoint_different_fields_verified() {
    let mut encoder = AYEncoder::new();
    let dt_ty = counter_ty();
    encoder
        .register_datatype("Counter", &counter_variants())
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "c".to_string(),
            ty: dt_ty.clone(),
        })
        .unwrap();

    let left = TrustVcPlace::root("c", dt_ty.clone()).field("count", i32_dt());
    let right = TrustVcPlace::root("c", dt_ty).field("max", i32_dt());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };

    let term = encoder.encode_condition_typed(&expr).unwrap();
    let negated = encoder.solver.try_not(term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "different fields on same root must be disjoint, negation should be unsat, got {:?}",
        result
    );
}

/// Different index vars on same seq → place_disjoint returns Compare(Ne, i, j).
/// When i != j is assumed, the disjointness holds.
#[test]
fn test_place_disjoint_different_indices_with_inequality() {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: seq_i32_ty(),
        })
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: i32_dt(),
        })
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "j".to_string(),
            ty: i32_dt(),
        })
        .unwrap();

    // Assume i != j
    let assume_ne = TrustVcExpr::Compare {
        op: CompareOp::Ne,
        left: Box::new(i32_var("i")),
        right: Box::new(i32_var("j")),
    };
    let ne_term = encoder.encode_condition_typed(&assume_ne).unwrap();
    encoder.solver.try_assert_term(ne_term).unwrap();

    // Assert disjoint(s[i], s[j])
    let left = TrustVcPlace::root("s", seq_i32_ty()).index(i32_var("i"), i32_dt());
    let right = TrustVcPlace::root("s", seq_i32_ty()).index(i32_var("j"), i32_dt());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };

    let term = encoder.encode_condition_typed(&expr).unwrap();
    let negated = encoder.solver.try_not(term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "s[i] and s[j] with i != j should be disjoint, negation should be unsat, got {:?}",
        result
    );
}

/// Same index on same seq → place_disjoint returns BoolLit(false).
#[test]
fn test_place_disjoint_same_index_not_disjoint() {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: seq_i32_ty(),
        })
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: i32_dt(),
        })
        .unwrap();

    let left = TrustVcPlace::root("s", seq_i32_ty()).index(i32_var("i"), i32_dt());
    let right = TrustVcPlace::root("s", seq_i32_ty()).index(i32_var("i"), i32_dt());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };

    let term = encoder.encode_condition_typed(&expr).unwrap();
    // BoolLit(false) → asserting it should be unsat
    encoder.solver.try_assert_term(term).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "s[i] and s[i] must NOT be disjoint (BoolLit(false)), asserting false should be unsat, got {:?}",
        result
    );
}

// ========================================================================
// ReadPlace encoding
// ========================================================================

/// ReadPlace on different datatype fields encodes without error and produces
/// distinct ay function applications (different selector names).
#[test]
fn test_read_place_different_fields_encode_without_error() {
    let mut encoder = AYEncoder::new();
    let dt_ty = counter_ty();
    encoder
        .register_datatype("Counter", &counter_variants())
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "c".to_string(),
            ty: dt_ty.clone(),
        })
        .unwrap();

    let count_place = TrustVcPlace::root("c", dt_ty.clone()).field("count", i32_dt());
    let max_place = TrustVcPlace::root("c", dt_ty).field("max", i32_dt());

    // Both field ReadPlaces must encode without error
    let count_read = TrustVcExpr::ReadPlace {
        place: count_place,
        ty: i32_dt(),
    };
    let max_read = TrustVcExpr::ReadPlace {
        place: max_place,
        ty: i32_dt(),
    };
    encoder
        .encode_condition_typed(&count_read)
        .expect("ReadPlace(c.count) should encode without error");
    encoder
        .encode_condition_typed(&max_read)
        .expect("ReadPlace(c.max) should encode without error");
}

/// ReadPlace on the same field twice produces the same ay term.
#[test]
fn test_read_place_same_field_consistent() {
    let mut encoder = AYEncoder::new();
    let dt_ty = counter_ty();
    encoder
        .register_datatype("Counter", &counter_variants())
        .unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "c".to_string(),
            ty: dt_ty.clone(),
        })
        .unwrap();

    let place1 = TrustVcPlace::root("c", dt_ty.clone()).field("count", i32_dt());
    let place2 = TrustVcPlace::root("c", dt_ty).field("count", i32_dt());

    let term1 = encoder
        .encode_condition_typed(&TrustVcExpr::ReadPlace {
            place: place1,
            ty: i32_dt(),
        })
        .unwrap();
    let term2 = encoder
        .encode_condition_typed(&TrustVcExpr::ReadPlace {
            place: place2,
            ty: i32_dt(),
        })
        .unwrap();

    // Assert term1 != term2 — should be UNSAT (same selector on same receiver)
    let ne = encoder.solver.try_neq(term1, term2).unwrap();
    encoder.solver.try_assert_term(ne).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "two ReadPlace(c.count) encodings must be equal, got {:?}",
        result
    );
}

/// ReadPlace on a root variable is just the variable itself.
#[test]
fn test_read_place_root_is_identity() {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_dt(),
        })
        .unwrap();

    // Assume x == 7
    let assume_expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(i32_var("x")),
        right: Box::new(TrustVcExpr::IntLit {
            value: 7,
            ty: i32_dt(),
        }),
    };
    let assume_term = encoder.encode_condition_typed(&assume_expr).unwrap();
    encoder.solver.try_assert_term(assume_term).unwrap();

    // Assert via ReadPlace: read(x) == 7
    let place = TrustVcPlace::root("x", i32_dt());
    let read_expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::ReadPlace {
            place,
            ty: i32_dt(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 7,
            ty: i32_dt(),
        }),
    };
    let assert_term = encoder.encode_condition_typed(&read_expr).unwrap();
    let negated = encoder.solver.try_not(assert_term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "ReadPlace on root should be identity encoding, got {:?}",
        result
    );
}
