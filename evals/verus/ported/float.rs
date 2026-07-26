// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/float.rs`.
//
// The upstream file exercises Verus float specs, float cast specs,
// nondeterministic cast behavior, unsupported f16/isize/usize diagnostics, and
// f32 bit-vector proof batches. TrustVc does not currently mirror those Verus
// specification surfaces as accepted replacement evidence.
//
// This scout keeps the manifest entry unsupported-gap and records only
// Rust-valid behavior TrustVc can execute today:
// - deterministic finite float arithmetic/comparison and cast checks, including
//   the executable shape of upstream f32_ieee true facts;
// - stable false cast/arithmetic probes that must produce counterexamples; and
// - direct f32 method/f16 uses as fail-closed unsupported boundaries.

#![allow(dead_code)]

pub const FLOAT_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "float_int_and_float_cast_self_consistency_verified",
        "int_to_f64_cast/int_to_f32_cast/float_to_float_cast Rust-valid cast theme",
        "verified",
        1,
    ),
    (
        "finite_float_casted_arithmetic_comparison_verified",
        "f32_ieee finite casted arithmetic/comparison true fact",
        "verified",
        1,
    ),
    (
        "f32_ieee_guarded_double_upper_bound_verified",
        "f32_ieee/test1 bounded double upper bound",
        "verified",
        1,
    ),
    (
        "f32_ieee_literal_add_commutes_verified",
        "f32_ieee/test1 literal addition commutativity",
        "verified",
        1,
    ),
    (
        "f32_ieee_literal_cast_equivalences_verified",
        "f32_ieee/test1 literal f32/u8/f64 cast facts",
        "verified",
        1,
    ),
    (
        "same_type_f64_literal_cast_identity_verified",
        "cast_same_float_identity",
        "verified",
        1,
    ),
    (
        "float_to_int_literal_round_trip_verified",
        "f64_to_int_cast Rust-valid literal cast theme",
        "verified",
        1,
    ),
    (
        "float_to_int_f32_i64_literal_round_trip_verified",
        "f32_to_int_cast Rust-valid literal cast theme",
        "verified",
        1,
    ),
    (
        "f32_clone_method_verified",
        "f32_basics non-NaN clone boundary",
        "verified",
        1,
    ),
    (
        "finite_float_casted_arithmetic_false_target_counterexample",
        "f32_ieee/test2 false finite casted arithmetic/comparison probe",
        "counterexample",
        1,
    ),
    (
        "f32_ieee_guarded_double_upper_bound_false_counterexample",
        "f32_ieee/test2 false guarded double upper bound",
        "counterexample",
        1,
    ),
    (
        "f32_ieee_guarded_add_wrong_sum_counterexample",
        "f32_ieee/test3 false guarded sum equality",
        "counterexample",
        1,
    ),
    (
        "float_to_int_literal_false_target_counterexample",
        "f32_ieee/test6 false float-to-int literal cast equality probe",
        "counterexample",
        1,
    ),
    (
        "float_int_to_float_false_target_counterexample",
        "f32_ieee/test7 false int-to-float literal cast equality probe",
        "counterexample",
        1,
    ),
    (
        "f64_to_f32_literal_false_target_counterexample",
        "f32_ieee/test8 false f64-to-f32 literal cast equality probe",
        "counterexample",
        1,
    ),
    (
        "f32_to_f64_literal_false_target_counterexample",
        "f32_ieee/test9 false f32-to-f64 literal cast equality probe",
        "counterexample",
        1,
    ),
    (
        "f32_is_finite_method_currently_blocked",
        "f32_basics is_finite_spec boundary",
        "error",
        0,
    ),
    (
        "float_to_bits_method_currently_blocked",
        "f32_basics f32_to_bits boundary",
        "error",
        0,
    ),
    (
        "cast_int_to_f16_currently_blocked",
        "cast_int_to_f16_unsupported",
        "error",
        0,
    ),
    (
        "cast_f16_to_int_currently_blocked",
        "cast_f16_to_int_unsupported",
        "error",
        0,
    ),
    (
        "cast_f16_to_f64_currently_blocked",
        "cast_f16_to_f64_unsupported",
        "error",
        0,
    ),
];

pub fn float_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    FLOAT_RS_EXPECTED_CASES
}

pub const FLOAT_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "f32_is_finite_method_currently_blocked",
        &[
            "is_finite() on type `f32`",
            "is_finite",
            "unsupported method",
        ],
    ),
    (
        "float_to_bits_method_currently_blocked",
        &["to_bits() on type `f32`", "to_bits", "unsupported method"],
    ),
    (
        "cast_int_to_f16_currently_blocked",
        &["f16", "unknown type", "unsupported"],
    ),
    (
        "cast_f16_to_int_currently_blocked",
        &["f16", "unknown type", "unsupported"],
    ),
    (
        "cast_f16_to_f64_currently_blocked",
        &["f16", "unknown type", "unsupported"],
    ),
];

pub fn float_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    FLOAT_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn float_int_and_float_cast_self_consistency_verified(seed: u32) {
    let widened_left = seed as f64;
    let widened_right = seed as f64;
    let four_as_f32 = 4u8 as f32;
    let five_as_f32 = 5u8 as f32;

    trust_vc::assert!(widened_left == widened_right);
    trust_vc::assert!(four_as_f32 < five_as_f32);
    trust_vc::assert!((four_as_f32 as f64) == (4u8 as f64));
}

#[trust_vc::ensures(true)]
fn finite_float_casted_arithmetic_comparison_verified() {
    let two = 2u8 as f32;
    let five = 5u8 as f32;
    let sum = two + two;

    trust_vc::assert!(sum == (4u8 as f32));
    trust_vc::assert!(sum <= five);
    trust_vc::assert!(two < five);
}

#[trust_vc::ensures(true)]
fn f32_ieee_guarded_double_upper_bound_verified(x: f32) {
    let low = 2u8 as f32;
    let high = 5u8 as f32;
    let max = 10u8 as f32;

    trust_vc::assert!(!((low <= x) && (x <= high)) || (x + x <= max));
}

#[trust_vc::ensures(true)]
fn f32_ieee_literal_add_commutes_verified() {
    let left = 2u8 as f32;
    let right = 5u8 as f32;

    trust_vc::assert!(left + right == right + left);
}

#[trust_vc::ensures(true)]
fn f32_ieee_literal_cast_equivalences_verified() {
    let four_u8 = 4u8;
    let four_as_f32 = four_u8 as f32;
    let four_as_f64 = four_u8 as f64;

    trust_vc::assert!((four_as_f32 as u8) == four_u8);
    trust_vc::assert!(four_as_f32 == (four_u8 as f32));
    trust_vc::assert!(four_as_f32 == (four_as_f64 as f32));
    trust_vc::assert!((four_as_f32 as f64) == four_as_f64);
}

#[trust_vc::ensures(true)]
fn same_type_f64_literal_cast_identity_verified() {
    let value = 4u8 as f64;
    let same = value as f64;

    trust_vc::assert!(value == same);
}

#[trust_vc::ensures(true)]
fn finite_float_casted_arithmetic_false_target_counterexample() {
    let two = 2u8 as f32;
    let five = 5u8 as f32;
    let sum = two + two;

    trust_vc::assert!(five < sum);
}

#[trust_vc::ensures(true)]
fn f32_ieee_guarded_double_upper_bound_false_counterexample(x: f32) {
    let low = 2u8 as f32;
    let high = 7u8 as f32;
    let max = 10u8 as f32;

    trust_vc::assert!(!((low <= x) && (x <= high)) || (x + x <= max));
}

#[trust_vc::ensures(true)]
fn f32_ieee_guarded_add_wrong_sum_counterexample(x: f32, y: f32) {
    let low = 2u8 as f32;
    let high = 5u8 as f32;

    trust_vc::assert!(!((low <= x) && (x <= high) && (low <= y) && (y <= high)) || (x + y == x + x));
}

#[trust_vc::ensures(true)]
fn float_int_to_float_false_target_counterexample() {
    trust_vc::assert!((4u8 as f32) == (5u8 as f32));
}

#[trust_vc::ensures(true)]
fn float_to_int_literal_round_trip_verified() {
    let four_as_f64 = 4u8 as f64;
    let four_again = four_as_f64 as u32;

    trust_vc::assert!(four_again == 4u32);
}

#[trust_vc::ensures(true)]
fn float_to_int_literal_false_target_counterexample() {
    let four_as_f64 = 4u8 as f64;
    let four_again = four_as_f64 as u32;

    trust_vc::assert!(four_again == 5u32);
}

#[trust_vc::ensures(true)]
fn float_to_int_f32_i64_literal_round_trip_verified() {
    let four_as_f32 = 4u8 as f32;
    let four_again = four_as_f32 as i64;

    trust_vc::assert!(four_again == 4i64);
}

#[trust_vc::ensures(true)]
fn f64_to_f32_literal_false_target_counterexample() {
    trust_vc::assert!((4u8 as f32) == ((5u8 as f64) as f32));
}

#[trust_vc::ensures(true)]
fn f32_to_f64_literal_false_target_counterexample() {
    trust_vc::assert!(((4u8 as f32) as f64) == (5u8 as f64));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(value == value)]
fn f32_clone_method_verified(value: f32) {
    let cloned = value.clone();

    trust_vc::assert!(cloned == value);
}

#[trust_vc::ensures(true)]
fn f32_is_finite_method_currently_blocked(value: f32) {
    let finite = value.is_finite();

    trust_vc::assert!(finite || !finite);
}

#[trust_vc::ensures(true)]
fn float_to_bits_method_currently_blocked(value: f32) {
    let bits = value.to_bits();

    trust_vc::assert!(bits == bits);
}

#[trust_vc::ensures(true)]
fn cast_int_to_f16_currently_blocked(value: i32) {
    let half: f16 = value as f16;

    trust_vc::assert!(half == half);
}

#[trust_vc::ensures(true)]
fn cast_f16_to_int_currently_blocked(value: i32) {
    let half: f16 = value as f16;
    let narrowed = half as i32;

    trust_vc::assert!(narrowed == narrowed);
}

#[trust_vc::ensures(true)]
fn cast_f16_to_f64_currently_blocked(value: i32) {
    let half: f16 = value as f16;
    let widened = half as f64;

    trust_vc::assert!(widened == widened);
}
