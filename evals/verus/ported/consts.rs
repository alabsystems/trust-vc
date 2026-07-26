// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused partial executable TrustVc port for upstream `consts.rs`.
//!
//! This file covers only Rust-valid slices of the upstream const/static
//! surface: local constant-expression arithmetic, a const-fn return-contract
//! witness, a nullary spec-function surrogate for an upstream `spec const`,
//! local fixed-array witnesses for upstream const-array reads, top-level scalar
//! const item reads, top-level literal usize const array lengths, and
//! fail-closed witnesses for static item handling.
//! Verus-only `exec const`, `spec const`, `exec static`, `when_used_as_spec`,
//! external-body consts, associated exec consts, atomics, proof-mode reads, and
//! exact diagnostic parity remain unsupported here.

#![allow(dead_code)]

use trust_vc_types::{int, View};

pub type ConstsRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ConstsRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CONSTS_RS_EXPECTED_CASES: &[ConstsRsExpectedCase] = &[
    ("const_arithmetic_value_verified", "test1", "verified", 1),
    (
        "const_fn_return_contract_verified",
        "test1 const fn e",
        "verified",
        1,
    ),
    (
        "spec_constant_surrogate_verified",
        "test1 spec const S",
        "verified",
        1,
    ),
    (
        "const_array_literal_exec_index_verified",
        "arrays",
        "verified",
        1,
    ),
    ("const_item_value_read_verified", "test1", "verified", 2),
    (
        "const_item_array_length_verified",
        "test_generic_const_eval2",
        "verified",
        2,
    ),
    (
        "const_arithmetic_wrong_value_counterexample",
        "test1_fails1",
        "counterexample",
        1,
    ),
    (
        "const_fn_return_contract_wrong_counterexample",
        "test1 const fn e false return contract",
        "counterexample",
        1,
    ),
    (
        "spec_constant_surrogate_wrong_counterexample",
        "test1_fails1 spec const S",
        "counterexample",
        1,
    ),
    (
        "const_array_literal_wrong_value_counterexample",
        "array_incorrect_value",
        "counterexample",
        1,
    ),
    (
        "const_array_literal_out_of_bounds_counterexample",
        "array_out_of_bounds",
        "counterexample",
        1,
    ),
    (
        "const_item_value_read_wrong_counterexample",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "static_item_value_read_currently_fails_closed",
        "statics_get_type_invariants",
        "error",
        0,
    ),
];

pub const CONSTS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ConstsRsFailClosedErrorPatterns] = &[(
    "static_item_value_read_currently_fails_closed",
    &[
        "unresolved variable `TOP_LEVEL_STATIC_VALUE`",
        "function parameter, let-binding, or quantifier-bound variable",
    ],
)];

pub fn consts_rs_expected_cases() -> &'static [ConstsRsExpectedCase] {
    CONSTS_RS_EXPECTED_CASES
}

pub fn consts_rs_fail_closed_error_patterns() -> &'static [ConstsRsFailClosedErrorPatterns] {
    CONSTS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

const TOP_LEVEL_CONST_VALUE: u64 = 3 + 5;
const CONST_ARRAY_LEN: usize = 3;
static TOP_LEVEL_STATIC_VALUE: u64 = 0;

#[trust_vc::spec]
fn spec_constant_value() -> int {
    9
}

#[trust_vc::ensures(true)]
fn const_arithmetic_value_verified() {
    let c: u64 = 3u64 + 5u64;
    trust_vc::assert!(c == 8u64);
}

#[trust_vc::ensures(true)]
fn const_arithmetic_wrong_value_counterexample() {
    let c: u64 = 3u64 + 5u64;
    trust_vc::assert!(c == 9u64);
}

#[trust_vc::returns(1u64)]
const fn const_fn_return_contract_verified() -> u64 {
    1
}

#[trust_vc::returns(2u64)]
const fn const_fn_return_contract_wrong_counterexample() -> u64 {
    1
}

#[trust_vc::ensures(true)]
fn spec_constant_surrogate_verified() {
    trust_vc::assert!(spec_constant_value() == 9);
}

#[trust_vc::ensures(true)]
fn spec_constant_surrogate_wrong_counterexample() {
    trust_vc::assert!(spec_constant_value() == 10);
}

#[trust_vc::ensures(true)]
fn const_array_literal_exec_index_verified() {
    let my_array = [1u32, 2u32, 3u32];
    let x = my_array[1usize];
    trust_vc::assert!(my_array.view().len() == 3usize);
    trust_vc::assert!(x == 2u32);
}

#[trust_vc::ensures(true)]
fn const_array_literal_wrong_value_counterexample() {
    let my_array = [1u32, 2u32, 3u32];
    let x = my_array[1usize];
    trust_vc::assert!(x == 42u32);
}

#[trust_vc::ensures(true)]
fn const_array_literal_out_of_bounds_counterexample() {
    let my_array = [1u32, 2u32, 3u32];
    trust_vc::assert!(my_array[5usize] == 3u32);
}

#[trust_vc::ensures(true)]
fn const_item_value_read_verified() {
    let x = TOP_LEVEL_CONST_VALUE;
    trust_vc::assert!(x == 8u64);
}

#[trust_vc::ensures(true)]
fn const_item_value_read_wrong_counterexample() {
    let x = TOP_LEVEL_CONST_VALUE;
    trust_vc::assert!(x == 9u64);
}

#[trust_vc::ensures(true)]
fn const_item_array_length_verified(ar: [u8; CONST_ARRAY_LEN]) {
    trust_vc::assert!(ar.view().len() == 3usize);
    trust_vc::assert!(ar[0usize] == ar[0usize]);
}

#[trust_vc::ensures(true)]
fn static_item_value_read_currently_fails_closed() {
    let x = TOP_LEVEL_STATIC_VALUE;
    trust_vc::assert!(x == 0u64);
}
