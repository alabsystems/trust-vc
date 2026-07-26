// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused partial executable TrustVc port for upstream `generics.rs`.
//!
//! The upstream file mixes Rust-valid generic structure with Verus-only
//! const-generic spec functions/datatype impls, decorated type encodings,
//! primitive view/old-state syntax, and broadcast proof functions. This scout
//! keeps the replacement evidence narrow: generic function contracts, generic
//! spec-function value identity, generic struct field substitution/projection,
//! u8 range facts adjacent to const-generic ranges, stable false witnesses, and
//! fail-closed unsupported boundaries for const-generic values/arrays and
//! old-state projections.

#![allow(dead_code)]

pub const GENERICS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "generic_exec_identity_contract",
        "test_decorated_datatype_encodings",
        "verified",
        1,
    ),
    (
        "generic_exec_concrete_return_contract",
        "test_decorated_datatype_encodings",
        "verified",
        1,
    ),
    (
        "generic_spec_identity_u64_round_trip",
        "test_decorated_datatype_encodings",
        "verified",
        1,
    ),
    (
        "generic_struct_field_projection_preserves_payload",
        "test_generic_primitive_has_type",
        "verified",
        1,
    ),
    (
        "generic_struct_concrete_field_projection_preserves_value",
        "test_generic_primitive_has_type",
        "verified",
        1,
    ),
    (
        "generic_struct_bool_field_projection_preserves_value",
        "",
        "verified",
        1,
    ),
    (
        "u8_const_generic_range_upper_bound_verified",
        "",
        "verified",
        1,
    ),
    (
        "u8_broadcast_range_surrogate_verified",
        "",
        "verified",
        1,
    ),
    (
        "const_generic_array_parameter_currently_blocked",
        "const_generic",
        "verified",
        1,
    ),
    (
        "generic_struct_concrete_field_projection_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "generic_struct_field_projection_wrong_payload_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "generic_struct_bool_field_projection_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "u8_const_generic_range_strict_upper_bound_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "u16_broadcast_range_surrogate_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "const_generic_value_parameter_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "const_generic_bool_parameter_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "generic_old_state_projection_currently_blocked",
        "",
        "error",
        0,
    ),
];

pub const GENERICS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "const_generic_value_parameter_currently_blocked",
        &["unresolved variable `N`", "const generic", "unsupported"],
    ),
    (
        "const_generic_bool_parameter_currently_blocked",
        &["unresolved variable `B`", "const generic", "unsupported"],
    ),
    (
        "generic_old_state_projection_currently_blocked",
        &[
            "Unsupported old-state expression",
            "unsupported expression `macro`",
            "old!",
            "macro",
        ],
    ),
];

pub fn generics_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    GENERICS_RS_EXPECTED_CASES
}

pub fn generics_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    GENERICS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::spec]
fn generic_identity<T>(value: T) -> T {
    value
}

struct GenericBox<T> {
    value: T,
}

struct GenericTaggedBox<T> {
    value: u64,
    tag: T,
}

struct GenericBoolBox<T> {
    value: bool,
    tag: T,
}

#[trust_vc::ensures(result == value)]
fn generic_exec_identity_contract<T>(value: T) -> T {
    value
}

#[trust_vc::ensures(result == 7u64)]
fn generic_exec_concrete_return_contract<T>(_tag: T) -> u64 {
    7u64
}

#[trust_vc::ensures(true)]
fn generic_spec_identity_u64_round_trip() {
    trust_vc::assert!(generic_identity::<u64>(7u64) == 7u64);
}

#[trust_vc::ensures(true)]
fn generic_struct_field_projection_preserves_payload(payload: u64) {
    let wrapped = GenericBox::<u64> { value: payload };

    trust_vc::assert!(wrapped.value == payload);
}

#[trust_vc::ensures(true)]
fn generic_struct_concrete_field_projection_preserves_value(tag: bool) {
    let wrapped = GenericTaggedBox::<bool> { value: 7u64, tag };

    trust_vc::assert!(wrapped.value == 7u64);
}

#[trust_vc::ensures(true)]
fn generic_struct_bool_field_projection_preserves_value(tag: u8) {
    let wrapped = GenericBoolBox::<u8> { value: true, tag };

    trust_vc::assert!(wrapped.value);
}

#[trust_vc::ensures(true)]
fn u8_const_generic_range_upper_bound_verified(value: u8) {
    trust_vc::assert!(value <= 255u8);
}

#[trust_vc::ensures(true)]
fn u8_broadcast_range_surrogate_verified(value: u8) {
    trust_vc::assert!(value <= 255u8);
}

#[trust_vc::ensures(true)]
fn generic_struct_concrete_field_projection_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        GenericTaggedBox::<bool> {
            value: 7u64,
            tag: true,
        }
        .value == 8u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn generic_struct_field_projection_wrong_payload_counterexample() {
    trust_vc::assert_by_compute!(
        GenericBox::<u64> { value: 7u64 }.value == 8u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn generic_struct_bool_field_projection_wrong_counterexample() {
    trust_vc::assert_by_compute!(
        GenericBoolBox::<u8> {
            value: true,
            tag: 0u8,
        }
        .value == false;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn u8_const_generic_range_strict_upper_bound_counterexample() {
    trust_vc::assert_by_compute!(255u8 < 255u8; compute_only);
}

#[trust_vc::ensures(true)]
fn u16_broadcast_range_surrogate_counterexample() {
    trust_vc::assert_by_compute!(255u16 < 255u16; compute_only);
}

#[trust_vc::ensures(true)]
fn const_generic_array_parameter_currently_blocked<const N: usize>(_arr: [u8; N]) {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn const_generic_value_parameter_currently_blocked<const N: u8>() {
    trust_vc::assert!(N < 255u8);
}

#[trust_vc::ensures(true)]
fn const_generic_bool_parameter_currently_blocked<const B: bool>() {
    trust_vc::assert!(B);
}

#[trust_vc::ensures(true)]
fn generic_old_state_projection_currently_blocked(value: GenericBox<u64>) {
    trust_vc::assert!(trust_vc::old!(value).value == value.value);
}
