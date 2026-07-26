// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/user_defined_type_invariants.rs`.
//
// The upstream file exercises Verus-only user-defined type invariant support:
// invariant declaration diagnostics, invariant checks at constructors and
// assignments, mut-ref field restrictions, privacy/visibility checks,
// use_type_invariant assumptions, tracked/ghost modes, const params, enums, and
// new-mut-ref option behavior. TrustVc does not currently model that declaration
// or automatic invariant-checking surface.
//
// This scout keeps the manifest entry unsupported-gap and records only the
// Rust-valid executable behavior TrustVc can check today:
// - manual constructor/assignment assertions corresponding to the basic
//   `test_ctors`, `test_mut_ref_whole_ok`, and `test_normal_var_nested` shapes;
// - a manual equality-field assertion corresponding to the generic equality
//   invariant shape; and
// - false adjacent scalar constructor/equality witnesses that must produce
//   concrete counterexamples rather than Unknown manifest evidence.

#![allow(dead_code, unused_assignments, unused_variables)]

use trust_vc_types::int;

pub const USER_DEFINED_TYPE_INVARIANTS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "type_inv_ctor_manual_invariant_verified",
        "test_ctors",
        "verified",
        2,
    ),
    (
        "type_inv_field_assignment_preserves_verified",
        "test_mut_ref_whole_ok",
        "verified",
        2,
    ),
    (
        "type_inv_nested_assignment_preserves_verified",
        "test_normal_var_nested",
        "verified",
        2,
    ),
    (
        "type_inv_equal_fields_manual_verified",
        "test_with_generics",
        "verified",
        1,
    ),
    (
        "type_inv_ctor_bad_value_counterexample",
        "test_ctors",
        "counterexample",
        1,
    ),
    (
        "type_inv_equal_fields_bad_counterexample",
        "test_with_generics",
        "counterexample",
        1,
    ),
];

pub fn user_defined_type_invariants_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    USER_DEFINED_TYPE_INVARIANTS_RS_EXPECTED_CASES
}

#[derive(Clone, Copy)]
struct BoundedInt {
    i: int,
    j: int,
}

#[derive(Clone, Copy)]
struct NestedBoundedInt {
    x: BoundedInt,
}

#[derive(Clone, Copy)]
struct EqualInts {
    i: int,
    j: int,
}

pub fn test_ctor_runtime_manual_invariant_subset() {
    let x = BoundedInt { i: 10, j: 100 };

    assert!(x.i < 15);
    assert_eq!(x.j, 100);
}

pub fn test_nested_runtime_manual_invariant_subset() {
    let mut y = NestedBoundedInt {
        x: BoundedInt { i: 12, j: 25 },
    };

    y.x.i = 10;
    y.x.j = 25;
    assert!(y.x.i < 15);
    assert!((20..30).contains(&y.x.j));
}

fn type_inv_ctor_manual_invariant_verified() {
    let x = BoundedInt { i: 10, j: 100 };

    trust_vc::assert!(x.i < 15);
    trust_vc::assert!(x.j == 100);
}

fn type_inv_field_assignment_preserves_verified() {
    let mut x = BoundedInt { i: 10, j: 8 };

    x.i = 7;
    trust_vc::assert!(x.i < 15);
    trust_vc::assert!(x.j == 8);
}

fn type_inv_nested_assignment_preserves_verified() {
    let mut y = NestedBoundedInt {
        x: BoundedInt { i: 12, j: 25 },
    };

    y.x.i = 10;
    y.x.j = 25;
    trust_vc::assert!(y.x.i < 15);
    trust_vc::assert!(y.x.j >= 20 && y.x.j < 30);
}

fn type_inv_equal_fields_manual_verified() {
    let x = EqualInts { i: 5, j: 5 };

    trust_vc::assert!(x.i == x.j);
}

fn type_inv_ctor_bad_value_counterexample() {
    let i: int = 20;

    trust_vc::assert!(i == 10);
}

fn type_inv_equal_fields_bad_counterexample() {
    let i: int = 5;
    let j: int = 7;

    trust_vc::assert!(i == j);
}
