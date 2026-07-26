// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/ext_equal.rs`.
//
// This scout intentionally keeps the upstream manifest entry unsupported-gap.
// It covers only the Rust-valid equality surface TrustVc can express today:
// explicit `ext_eq!` over SpecFn closures and finite constructed collections,
// false extensional claims that must not verify, and a direct PartialEq method
// boundary for SpecFn equality that must fail closed until the broader Verus
// `#[verifier::auto_ext_equal]`, `=~=`, `=~~=`, and `#[verifier::ext_equal]`
// surfaces are modeled.

#![allow(dead_code)]

use trust_vc_types::{int, Map, Seq, Set, SpecFn};

pub const EXT_EQUAL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "ext_equal_spec_fn_int_successor_verified",
        "test_fn",
        "verified",
        1,
    ),
    (
        "ext_equal_seq_push_chain_verified",
        "test_seq",
        "verified",
        1,
    ),
    (
        "ext_equal_set_insert_order_verified",
        "test_set",
        "verified",
        1,
    ),
    (
        "ext_equal_map_insert_order_verified",
        "test_map",
        "verified",
        1,
    ),
    (
        "ext_equal_seq_wrong_length_counterexample",
        "test_seq_fails1",
        "counterexample",
        1,
    ),
    (
        "ext_equal_map_wrong_value_counterexample",
        "test_map_fails2",
        "counterexample",
        1,
    ),
    (
        "ext_equal_spec_fn_partial_eq_method_currently_blocked",
        "test_fn/test_fn_fails",
        "error",
        0,
    ),
];

pub fn ext_equal_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXT_EQUAL_RS_EXPECTED_CASES
}

pub const EXT_EQUAL_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "ext_equal_spec_fn_partial_eq_method_currently_blocked",
    &["unsupported method `eq() on type `SpecFn<int, int>`"],
)];

pub fn ext_equal_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    EXT_EQUAL_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn ext_equal_spec_fn_int_successor_verified() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|i: int| i + 1),
        SpecFn::new(|j: int| 1 + j)
    ));
}

#[trust_vc::ensures(true)]
fn ext_equal_seq_push_chain_verified() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<u8>::empty().push(9u8).push(10u8),
        Seq::<u8>::empty().push(9u8).push(10u8)
    ));
}

#[trust_vc::ensures(true)]
fn ext_equal_set_insert_order_verified() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<u8>::empty().insert(0u8).insert(1u8),
        Set::<u8>::empty().insert(1u8).insert(0u8)
    ));
}

#[trust_vc::ensures(true)]
fn ext_equal_map_insert_order_verified() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Map::<u8, bool>::empty()
            .insert(0u8, true)
            .insert(1u8, false),
        Map::<u8, bool>::empty()
            .insert(1u8, false)
            .insert(0u8, true)
    ));
}

#[trust_vc::ensures(true)]
fn ext_equal_seq_wrong_length_counterexample() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<u8>::empty().push(9u8),
        Seq::<u8>::empty().push(9u8).push(10u8)
    ));
}

#[trust_vc::ensures(true)]
fn ext_equal_map_wrong_value_counterexample() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Map::<u8, bool>::empty().insert(0u8, true),
        Map::<u8, bool>::empty().insert(0u8, false)
    ));
}

#[trust_vc::ensures(result)]
fn ext_equal_spec_fn_partial_eq_method_currently_blocked(
    left: SpecFn<int, int>,
    right: SpecFn<int, int>,
) -> bool {
    left.eq(&right)
}
