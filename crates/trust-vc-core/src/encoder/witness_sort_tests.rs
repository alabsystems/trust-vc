//! Unit pins for the broadcast witness sort gate.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use super::{
    binding_tuple_is_in_sort, instantiate_bound_vars_in_sort, term_sort_inhabits_type,
    value_inhabits_int_type, witness_inhabits_type,
};
use crate::ir::{TrustVcExpr, TrustVcType};
use ay_dpll::api::Sort;

fn u8_ty() -> TrustVcType {
    TrustVcType::Uint { width: 8 }
}
fn u64_ty() -> TrustVcType {
    TrustVcType::Uint { width: 64 }
}
fn i8_ty() -> TrustVcType {
    TrustVcType::Int { width: 8 }
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

fn int_lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

// ---------------------------------------------------------------------------
// SOUNDNESS PINS — out-of-sort witnesses must be rejected.
// ---------------------------------------------------------------------------

/// The round-1 defect: an out-of-range VALUE. Kept here because the value test
/// moved into this module and is now shared by every witness source.
#[test]
fn out_of_sort_values_are_rejected() {
    assert!(!value_inhabits_int_type(u64::MAX as i128, &u8_ty()));
    assert!(!value_inhabits_int_type(-1, &u8_ty()));
    assert!(!value_inhabits_int_type(256, &u8_ty()));
    assert!(!value_inhabits_int_type(i128::MIN, &u8_ty()));

    assert!(!value_inhabits_int_type(128, &i8_ty()));
    assert!(!value_inhabits_int_type(-129, &i8_ty()));
    assert!(!value_inhabits_int_type(u64::MAX as i128, &i8_ty()));

    assert!(!value_inhabits_int_type(-1, &TrustVcType::Nat));
}

/// THE SIBLING DEFECT. A witness harvested by matching a trigger pattern against
/// the goal is an arbitrary EXPRESSION, not a literal — and a wider-typed
/// expression substituted into a narrow bound variable asserts a consistent but
/// unjustified fact (`w <= 255` for an arbitrary `u64 w`). No value test can see
/// this; only the type test can.
#[test]
fn wider_typed_expression_witnesses_are_rejected() {
    // `forall|x: u8| ...` instantiated at a `u64` variable.
    assert!(!witness_inhabits_type(&var("w", u64_ty()), &u8_ty()));
    // ... at a `u64`-typed arithmetic expression.
    assert!(!witness_inhabits_type(
        &TrustVcExpr::Arith {
            op: crate::ir::ArithOp::Mul,
            left: Box::new(var("w", u64_ty())),
            right: Box::new(var("w", u64_ty())),
            ty: u64_ty(),
        },
        &u8_ty()
    ));
    // Signedness matters as much as width: an `i8` can be negative.
    assert!(!witness_inhabits_type(&var("s", i8_ty()), &u8_ty()));
    // An unbounded `int` is not included in any finite width.
    assert!(!witness_inhabits_type(
        &var("n", TrustVcType::MathInt),
        &u64_ty()
    ));
    // A possibly-negative source is not a `nat`.
    assert!(!witness_inhabits_type(
        &var("s", i8_ty()),
        &TrustVcType::Nat
    ));
    // Cross-sort: a Bool bound variable cannot take an integer witness.
    assert!(!witness_inhabits_type(
        &var("w", u64_ty()),
        &TrustVcType::Bool
    ));
    // Cross-sort the other way: a `Seq<u8>` witness is not a `u8`.
    assert!(!witness_inhabits_type(
        &var("s", TrustVcType::Seq(Box::new(u8_ty()))),
        &u8_ty()
    ));
}

/// A bound variable whose type is not declared DECLINES: the sort cannot be
/// established, so the substitution cannot be shown to be an instantiation.
#[test]
fn undeclared_bound_var_declines() {
    let witnesses = vec![int_lit(3, u8_ty())];
    let empty: HashMap<String, TrustVcType> = HashMap::new();
    assert!(!binding_tuple_is_in_sort(
        &["x".to_string()],
        &witnesses,
        &empty
    ));
    assert!(instantiate_bound_vars_in_sort(
        &var("x", u8_ty()),
        &["x".to_string()],
        &witnesses,
        &empty
    )
    .is_none());
}

/// Arity disagreement declines rather than silently substituting a prefix.
#[test]
fn arity_mismatch_declines() {
    let mut types = HashMap::new();
    types.insert("x".to_string(), u8_ty());
    types.insert("y".to_string(), u8_ty());
    assert!(!binding_tuple_is_in_sort(
        &["x".to_string(), "y".to_string()],
        &[int_lit(1, u8_ty())],
        &types
    ));
}

/// The whole tuple is refused when ANY position is out of sort — a partial
/// substitution would leave a free bound variable in the asserted "ground" fact.
#[test]
fn one_bad_position_refuses_the_whole_tuple() {
    let mut types = HashMap::new();
    types.insert("x".to_string(), u8_ty());
    types.insert("y".to_string(), u8_ty());
    let witnesses = vec![int_lit(1, u8_ty()), var("w", u64_ty())];
    assert!(!binding_tuple_is_in_sort(
        &["x".to_string(), "y".to_string()],
        &witnesses,
        &types
    ));
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the gate must not be "decline everything".
// ---------------------------------------------------------------------------

#[test]
fn in_sort_values_are_kept() {
    for value in [0i128, 1, 7, 128, 254, 255] {
        assert!(
            value_inhabits_int_type(value, &u8_ty()),
            "{value} is a u8 and must survive the gate"
        );
    }
    for value in [-128i128, -1, 0, 1, 127] {
        assert!(value_inhabits_int_type(value, &i8_ty()), "{value} is an i8");
    }
    assert!(value_inhabits_int_type(u64::MAX as i128, &u64_ty()));
    assert!(!value_inhabits_int_type(-1, &u64_ty()));
    assert!(value_inhabits_int_type(i128::MIN, &TrustVcType::MathInt));
    assert!(value_inhabits_int_type(i128::MAX, &TrustVcType::MathInt));
    assert!(value_inhabits_int_type(0, &TrustVcType::Nat));
}

/// The instantiations a legitimate broadcast lemma actually needs.
#[test]
fn in_sort_expression_witnesses_are_kept() {
    // Same type — the overwhelmingly common case.
    assert!(witness_inhabits_type(&var("a", u8_ty()), &u8_ty()));
    assert!(witness_inhabits_type(&var("a", u64_ty()), &u64_ty()));
    // Narrower into wider, same signedness.
    assert!(witness_inhabits_type(&var("a", u8_ty()), &u64_ty()));
    assert!(witness_inhabits_type(
        &var("a", TrustVcType::Int { width: 8 }),
        &TrustVcType::Int { width: 32 }
    ));
    // Unsigned into a strictly wider signed type.
    assert!(witness_inhabits_type(
        &var("a", TrustVcType::Uint { width: 32 }),
        &TrustVcType::Int { width: 64 }
    ));
    // `forall|i: int| ...` instantiated at a `usize` index — the pattern spec
    // code relies on constantly.
    assert!(witness_inhabits_type(
        &var("i", TrustVcType::Uint { width: 64 }),
        &TrustVcType::MathInt
    ));
    assert!(witness_inhabits_type(
        &var("i", TrustVcType::Uint { width: 64 }),
        &TrustVcType::Nat
    ));
    // A literal whose declared type is wide but whose VALUE fits stays usable.
    assert!(witness_inhabits_type(&int_lit(7, u64_ty()), &u8_ty()));
    // Bool.
    assert!(witness_inhabits_type(
        &TrustVcExpr::BoolLit(true),
        &TrustVcType::Bool
    ));
    // Container sorts pass on backend-sort agreement.
    let seq_u8 = TrustVcType::Seq(Box::new(u8_ty()));
    assert!(witness_inhabits_type(&var("s", seq_u8.clone()), &seq_u8));
    // Type-erased bound variables accept anything (polymorphic ground replay).
    assert!(witness_inhabits_type(
        &var("w", u64_ty()),
        &TrustVcType::TypeParam("T".to_string())
    ));
    assert!(witness_inhabits_type(
        &var("w", u64_ty()),
        &TrustVcType::Poly
    ));
}

/// The gate must actually substitute when everything is in sort — otherwise the
/// soundness pins above would pass on a no-op.
#[test]
fn in_sort_tuple_substitutes() {
    let mut types = HashMap::new();
    types.insert("x".to_string(), u8_ty());
    let body = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Le,
        left: Box::new(var("x", u8_ty())),
        right: Box::new(int_lit(255, u8_ty())),
    };
    let instance =
        instantiate_bound_vars_in_sort(&body, &["x".to_string()], &[int_lit(7, u8_ty())], &types)
            .expect("an in-sort witness must instantiate");
    assert_ne!(instance, body, "substitution must have happened");
}

/// The fixed type-boundary battery must survive the gate, or the whole premise
/// silently yields no instances.
#[test]
fn every_type_boundary_survives_the_gate() {
    for ty in [
        TrustVcType::Uint { width: 8 },
        TrustVcType::Uint { width: 16 },
        TrustVcType::Uint { width: 32 },
        TrustVcType::Uint { width: 64 },
        TrustVcType::Int { width: 8 },
        TrustVcType::Int { width: 32 },
        TrustVcType::Int { width: 64 },
        TrustVcType::MathInt,
        TrustVcType::Nat,
    ] {
        let boundaries =
            crate::encoder::verification::broadcast_model_revalidation::int_type_boundaries(&ty);
        assert!(!boundaries.is_empty(), "no boundaries for {ty:?}");
        for value in boundaries {
            assert!(
                value_inhabits_int_type(value, &ty),
                "boundary {value} rejected for {ty:?}"
            );
            assert!(
                witness_inhabits_type(&int_lit(value, ty.clone()), &ty),
                "boundary {value} rejected by the expression gate for {ty:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Term-level gate (S7).
// ---------------------------------------------------------------------------

#[test]
fn term_sort_gate_rejects_width_mismatch() {
    assert!(!term_sort_inhabits_type(&Sort::bitvec(64), &u8_ty()));
    assert!(!term_sort_inhabits_type(&Sort::Bool, &u8_ty()));
    assert!(!term_sort_inhabits_type(
        &Sort::bitvec(8),
        &TrustVcType::Bool
    ));
}

#[test]
fn term_sort_gate_keeps_matching_sorts() {
    assert!(term_sort_inhabits_type(&Sort::bitvec(8), &u8_ty()));
    assert!(term_sort_inhabits_type(&Sort::bitvec(64), &u64_ty()));
    assert!(term_sort_inhabits_type(&Sort::Bool, &TrustVcType::Bool));
    assert!(term_sort_inhabits_type(&Sort::Int, &TrustVcType::MathInt));
    assert!(term_sort_inhabits_type(&Sort::Int, &TrustVcType::Nat));
    // An `int` bound variable takes a bitvector-represented integer term.
    assert!(term_sort_inhabits_type(
        &Sort::bitvec(64),
        &TrustVcType::MathInt
    ));
    // Type-erased.
    assert!(term_sort_inhabits_type(
        &Sort::bitvec(64),
        &TrustVcType::TypeParam("T".to_string())
    ));
}
