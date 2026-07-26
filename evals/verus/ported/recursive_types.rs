// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/recursive_types.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally records
// only stable evidence TrustVc can execute today:
// - Rust-valid recursive enum declarations through Box, including struct
//   wrapper payloads and a mutual-recursion declaration shape;
// - boxed-payload constructor/ownership smoke tests that do not claim payload
//   inspection or branch-refinement support;
// - a small decreases-adjacent compute witness kept separate from recursive
//   datatype well-foundedness; and
// - stable false-claim counterexamples for the same narrow executable slice.
//
// Full upstream parity remains unsupported: Verus recursive-type positivity
// attributes, external_body recursive-type parameter annotations, boxed payload
// inspection/refinement, function-spec positivity diagnostics, and exact
// diagnostic text are fail-closed boundaries rather than replacement claims.

#![allow(dead_code, unused_variables)]

use trust_vc_types::nat;

pub const UPSTREAM_RECURSIVE_TYPES_RS_PINNED_CASES: &[&str] = &[
    "test1",
    "test2",
    "test3",
    "test4",
    "test1_ok",
    "test1_fails",
    "test2_ok",
    "test2_fails",
    "test3_ok",
    "test3_fails",
    "test5_ok",
    "test5_fails1",
    "test5_fails2",
    "test5_fails3",
    "lifetimes_no_positivity",
    "fnspec_positivity",
];

pub fn upstream_recursive_types_rs_pinned_cases() -> &'static [&'static str] {
    UPSTREAM_RECURSIVE_TYPES_RS_PINNED_CASES
}

pub type RecursiveTypesRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type RecursiveTypesRsExpectedErrorPattern = (&'static str, &'static [&'static str]);

pub const RECURSIVE_TYPES_RS_EXPECTED_CASES: &[RecursiveTypesRsExpectedCase] = &[
    (
        "recursive_enum_constructor_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_struct_wrapper_field_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_box_variant_constructor_smoke_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_box_payload_opaque_transfer_verified",
        "",
        "verified",
        3,
    ),
    (
        "mutually_recursive_enum_constructor_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_type_decrease_adjacent_countdown_verified",
        "",
        "verified",
        1,
    ),
    (
        "recursive_enum_wrong_variant_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_box_variant_wrong_outer_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_struct_wrapper_wrong_field_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "mutually_recursive_enum_wrong_variant_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_type_decrease_adjacent_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "recursive_type_reject_recursive_types_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_external_body_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_external_body_missing_reject_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_boxed_payload_local_inspector_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_fnspec_positivity_diagnostic_currently_errors",
        "",
        "error",
        0,
    ),
];

pub fn recursive_types_rs_expected_cases() -> &'static [RecursiveTypesRsExpectedCase] {
    RECURSIVE_TYPES_RS_EXPECTED_CASES
}

pub const RECURSIVE_TYPES_RS_EXPECTED_ERROR_PATTERNS: &[RecursiveTypesRsExpectedErrorPattern] = &[
    (
        "recursive_type_reject_recursive_types_attr_currently_errors",
        &["Unsupported nested struct item", "nested items are rejected"],
    ),
    (
        "recursive_type_external_body_attr_currently_errors",
        &["Unsupported nested struct item", "nested items are rejected"],
    ),
    (
        "recursive_type_external_body_missing_reject_attr_currently_errors",
        &["Unsupported nested struct item", "nested items are rejected"],
    ),
    (
        "recursive_type_boxed_payload_local_inspector_currently_errors",
        &["Unsupported nested fn item", "nested items are rejected"],
    ),
    (
        "recursive_type_fnspec_positivity_diagnostic_currently_errors",
        &["Unsupported nested struct item", "nested items are rejected"],
    ),
];

pub fn recursive_types_rs_expected_error_patterns(
) -> &'static [RecursiveTypesRsExpectedErrorPattern] {
    RECURSIVE_TYPES_RS_EXPECTED_ERROR_PATTERNS
}

struct List<A> {
    a: A,
}

enum E1 {
    N,
    E(Box<E1>),
    F(List<Box<E1>>),
}

enum E2 {
    N,
    E(Box<E1>),
}

enum M1 {
    N,
    E(Box<M2>),
    F(List<Box<M2>>),
}

enum M2 {
    N,
    E(Box<M1>),
}

#[trust_vc::decreases(fuel)]
#[trust_vc::spec]
fn recursive_type_decrease_adjacent_fuel(fuel: nat) -> nat {
    if fuel == 0 {
        0
    } else {
        1 + recursive_type_decrease_adjacent_fuel((fuel - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn recursive_enum_constructor_match_all_branches_safe() {
    let value = E1::N;

    match value {
        E1::N => trust_vc::assert!(true),
        E1::E(_) => trust_vc::assert!(true),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_struct_wrapper_field_match_all_branches_safe() {
    let wrapped = List { a: E1::N };

    match wrapped.a {
        E1::N => trust_vc::assert!(true),
        E1::E(_) => trust_vc::assert!(true),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_box_variant_constructor_smoke_safe() {
    let value = E1::E(Box::new(E1::N));

    match value {
        E1::N => trust_vc::assert!(true),
        E1::E(_) => trust_vc::assert!(true),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_box_payload_opaque_transfer_verified() {
    let value = E1::E(Box::new(E1::N));

    match value {
        E1::N => trust_vc::assert!(true),
        E1::E(inner) => {
            let _payload = inner;
            trust_vc::assert!(true);
        }
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn mutually_recursive_enum_constructor_match_all_branches_safe() {
    let value = M1::N;

    match value {
        M1::N => trust_vc::assert!(true),
        M1::E(_) => trust_vc::assert!(true),
        M1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_type_decrease_adjacent_countdown_verified() {
    let _seed = E1::E(Box::new(E1::N));

    trust_vc::assert_by_compute!(
        recursive_type_decrease_adjacent_fuel(3 as nat) == (3 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn recursive_enum_wrong_variant_counterexample() {
    let value = E1::N;

    match value {
        E1::N => trust_vc::assert!(false),
        E1::E(_) => trust_vc::assert!(true),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_box_variant_wrong_outer_counterexample() {
    let value = E1::E(Box::new(E1::N));

    match value {
        E1::N => trust_vc::assert!(true),
        E1::E(_) => trust_vc::assert!(false),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_struct_wrapper_wrong_field_counterexample() {
    let wrapped = List { a: E1::N };

    match wrapped.a {
        E1::N => trust_vc::assert!(false),
        E1::E(_) => trust_vc::assert!(true),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn mutually_recursive_enum_wrong_variant_counterexample() {
    let value = M1::N;

    match value {
        M1::N => trust_vc::assert!(false),
        M1::E(_) => trust_vc::assert!(true),
        M1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_type_decrease_adjacent_wrong_value_counterexample() {
    let _seed = E1::E(Box::new(E1::N));

    trust_vc::assert_by_compute!(
        recursive_type_decrease_adjacent_fuel(3 as nat) == (4 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn recursive_type_reject_recursive_types_attr_currently_errors() {
    #[verifier::reject_recursive_types(A)]
    struct RejectRecursiveTypesList<A> {
        a: A,
    }

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn recursive_type_external_body_attr_currently_errors() {
    #[verifier(external_body)]
    #[verifier::reject_recursive_types(K)]
    #[verifier::accept_recursive_types(V)]
    struct ExternalBodyMap<K, V> {
        dummy: core::marker::PhantomData<(K, V)>,
    }

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn recursive_type_external_body_missing_reject_attr_currently_errors() {
    #[verifier(external_body)]
    #[verifier::reject_recursive_types(K)]
    #[verifier::accept_recursive_types(V)]
    struct ExternalBodyMap<K, V> {
        dummy: core::marker::PhantomData<(K, V)>,
    }

    struct ExternalBodyD<A, B> {
        d: ExternalBodyMap<i64, ExternalBodyD<A, B>>,
        a: ExternalBodyMap<A, i64>,
        b: ExternalBodyMap<i64, B>,
    }

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn recursive_type_boxed_payload_local_inspector_currently_errors() {
    fn inspect_payload(payload: Box<E1>) -> bool {
        matches!(*payload, E1::N)
    }

    let value = E1::E(Box::new(E1::N));

    match value {
        E1::N => trust_vc::assert!(false),
        E1::E(inner) => trust_vc::assert!(inspect_payload(inner)),
        E1::F(_) => trust_vc::assert!(true),
    }
}

#[trust_vc::ensures(true)]
fn recursive_type_fnspec_positivity_diagnostic_currently_errors() {
    struct FnSpecPositivityBoundary {
        f: fn(FnSpecPositivityBoundary) -> i64,
    }

    trust_vc::assert!(true);
}
