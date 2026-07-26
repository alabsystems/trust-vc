// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream operators.rs.
//
// This file intentionally covers only small Rust-valid slices of the upstream
// operator corpus: signed division/remainder behavior, concrete comparison and
// logical operators, primitive shift-width guards, derived structural equality,
// primitive integer Add::add lowering, and fail-closed custom trait-method
// witnesses.
// External trait specifications, vstd operator spec traits, structural equality
// priority over assumed specifications, overloaded PartialEq/Sub contracts,
// non-primitive trait method lowering, and exact Verus diagnostics remain
// unsupported.

#![allow(dead_code)]

use core::ops::Add;

pub const OPERATORS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "signed_division_rounds_toward_zero_verified",
        "test_arith/test_signed_div",
        "verified",
        4,
    ),
    (
        "signed_remainder_keeps_dividend_sign_verified",
        "test_arith/test_signed_mod",
        "verified",
        4,
    ),
    (
        "comparison_and_logical_operators_verified",
        "test_arith/test_eq_ineq",
        "verified",
        8,
    ),
    (
        "shift_left_in_range_u16_verified",
        "test_arith/test_shl",
        "verified",
        1,
    ),
    (
        "shift_right_in_range_i16_verified",
        "test_arith/test_shr",
        "verified",
        1,
    ),
    (
        "derived_structural_equality_verified",
        "test_structural_eq",
        "verified",
        3,
    ),
    (
        "boolean_logical_operator_wrong_counterexample",
        "test_arith/test_eq_ineq",
        "counterexample",
        1,
    ),
    (
        "primitive_integer_add_method_verified",
        "test_integer_using_trait_add",
        "verified",
        2,
    ),
    (
        "custom_partial_eq_method_currently_blocked",
        "test_eq_overload",
        "error",
        0,
    ),
];

pub const OPERATORS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "custom_partial_eq_method_currently_blocked",
    &[
        "eq",
        "PartialEq",
        "unsupported",
        "unknown",
        "opaque",
        "unresolved",
    ],
)];

pub fn operators_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    OPERATORS_RS_EXPECTED_CASES
}

pub fn operators_rs_fail_closed_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    OPERATORS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct OperatorStructuralRecord {
    a: u8,
    b: usize,
    c: bool,
}

#[derive(Clone, Copy, Eq)]
struct OperatorCustomPartialEq {
    value: u8,
}

impl PartialEq for OperatorCustomPartialEq {
    fn eq(&self, other: &Self) -> bool {
        self.value != other.value
    }
}

#[trust_vc::ensures(true)]
fn primitive_integer_add_method_verified() {
    let a: usize = 2;
    let b: usize = 3;
    let c1 = a + b;
    let c2 = a.add(b);

    trust_vc::assert!(c1 == 5);
    trust_vc::assert!(c1 == c2);
}

#[trust_vc::ensures(true)]
fn signed_division_rounds_toward_zero_verified() {
    let x1 = 53i8 / 10i8;
    let x2 = (-53i8) / 10i8;
    let x3 = 53i8 / (-10i8);
    let x4 = (-53i8) / (-10i8);

    trust_vc::assert!(x1 == 5);
    trust_vc::assert!(x2 == -5);
    trust_vc::assert!(x3 == -5);
    trust_vc::assert!(x4 == 5);
}

#[trust_vc::ensures(true)]
fn signed_remainder_keeps_dividend_sign_verified() {
    let x1 = 53i8 % 10i8;
    let x2 = (-53i8) % 10i8;
    let x3 = 53i8 % (-10i8);
    let x4 = (-53i8) % (-10i8);

    trust_vc::assert!(x1 == 3);
    trust_vc::assert!(x2 == -3);
    trust_vc::assert!(x3 == 3);
    trust_vc::assert!(x4 == -3);
}

#[trust_vc::ensures(true)]
fn comparison_and_logical_operators_verified() {
    let low = -4i32;
    let mid = 0i32;
    let high = 9i32;

    trust_vc::assert!(low < mid);
    trust_vc::assert!(mid <= high);
    trust_vc::assert!(high > low);
    trust_vc::assert!(high >= mid);
    trust_vc::assert!(mid == 0i32);
    trust_vc::assert!(low != high);
    trust_vc::assert!((low < mid && high > mid) || low == high);
    trust_vc::assert!(!(high < low));
}

#[trust_vc::ensures(true)]
fn shift_left_in_range_u16_verified(x: u16) {
    let y = 15u16;
    trust_vc::assert!(x << y == x << y);
}

#[trust_vc::ensures(true)]
fn shift_right_in_range_i16_verified(x: i16) {
    let y = 15i16;
    trust_vc::assert!(x >> y == x >> y);
}

#[trust_vc::ensures(true)]
fn derived_structural_equality_verified(a: u8, b: usize) {
    let left = OperatorStructuralRecord { a, b, c: true };
    let same = OperatorStructuralRecord { a, b, c: true };
    let different = OperatorStructuralRecord { a, b, c: false };

    trust_vc::assert!(left == same);
    trust_vc::assert!(left != different);
    trust_vc::assert!((left == same) && !(left == different));
}

fn boolean_logical_operator_wrong_counterexample() {
    trust_vc::assert!(true && !true);
}

#[trust_vc::ensures(true)]
fn custom_partial_eq_method_currently_blocked() {
    let left = OperatorCustomPartialEq { value: 1 };
    let right = OperatorCustomPartialEq { value: 2 };

    trust_vc::assert!(left.eq(&right));
}
