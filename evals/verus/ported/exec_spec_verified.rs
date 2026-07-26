// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc port for upstream exec_spec_verified.rs.
//
// The upstream file exercises the Verus `exec_spec_verified!` macro, which
// generates executable wrappers and specification-side contracts from spec
// definitions. TrustVc has no direct macro equivalent, so this file covers
// Rust-valid scalar and record surfaces: source spec functions plus manually
// written executable wrappers whose postconditions state that they return the
// spec value. It also pins the unsupported boundary where an executable helper
// is used as a specification expression.
//
// Full parity remains unsupported: generated Exec* datatypes, SpecString,
// collection conversions, quantifier bounds, recursive decreases, and macro
// span diagnostics are outside this slice.

#![allow(dead_code)]

pub type ExecSpecVerifiedExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ExecSpecVerifiedFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const EXEC_SPEC_VERIFIED_RS_EXPECTED_CASES: &[ExecSpecVerifiedExpectedCase] = &[
    (
        "exec_exec_spec_verified_id_u32",
        "test_exec_spec_typing_id_u32",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_literal_true",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_literal_i32",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_square_bounded",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_usize_eq",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_option_u8_eq",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_constant_usize_max_minus",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_pred",
        "test_exec_spec_interop2_pred",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_literal_i32_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_exec_spec_verified_square_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_exec_spec_verified_constant_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_spec_verified_generated_u32_wrapper_caller_fails_closed",
        "test_exec_spec_typing_generated_wrapper_call",
        "verified",
        1,
    ),
    (
        "exec_spec_verified_generated_pred_wrapper_caller_fails_closed",
        "test_exec_spec_interop2_generated_wrapper_call",
        "verified",
        1,
    ),
    (
        "exec_spec_verified_exec_wrapper_in_contract_fails_closed",
        "test_exec_spec_verified_generated_exec_helper_as_spec_term",
        "error",
        0,
    ),
    (
        "exec_exec_spec_verified_struct_pred_fails_closed",
        "",
        "verified",
        1,
    ),
];

pub const EXEC_SPEC_VERIFIED_RS_FAIL_CLOSED_ERROR_PATTERNS:
    &[ExecSpecVerifiedFailClosedErrorPatterns] = &[
    (
        "exec_spec_verified_exec_wrapper_in_contract_fails_closed",
        &["Unsupported call to sibling helper"],
    ),
];

pub fn exec_spec_verified_rs_expected_cases() -> &'static [ExecSpecVerifiedExpectedCase] {
    EXEC_SPEC_VERIFIED_RS_EXPECTED_CASES
}

pub fn exec_spec_verified_rs_fail_closed_error_patterns(
) -> &'static [ExecSpecVerifiedFailClosedErrorPatterns] {
    EXEC_SPEC_VERIFIED_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy)]
struct ExecSpecVerifiedA {
    a: u32,
    b: u32,
}

#[trust_vc::spec]
fn exec_spec_verified_id_u32(x: u32) -> u32 {
    x
}

#[trust_vc::spec]
fn exec_spec_verified_literal_true() -> bool {
    true
}

#[trust_vc::spec]
fn exec_spec_verified_literal_i32() -> i32 {
    123i32
}

#[trust_vc::spec]
#[trust_vc::recommends(x <= 0xffffu32)]
fn exec_spec_verified_square_bounded(x: u32) -> u32 {
    x * x
}

#[trust_vc::spec]
fn exec_spec_verified_usize_eq(i: usize, j: usize) -> bool {
    if i == j {
        true
    } else {
        false
    }
}

#[trust_vc::spec]
fn exec_spec_verified_option_u8_eq(a: Option<u8>, b: Option<u8>) -> bool {
    if a == b {
        true
    } else {
        false
    }
}

#[trust_vc::spec]
fn exec_spec_verified_constant_usize_max_minus(i: usize) -> bool {
    if usize::MAX - i != 0usize {
        true
    } else {
        false
    }
}

#[trust_vc::spec]
fn exec_spec_verified_pred(a: u32, b: u32) -> bool {
    a > b
}

#[trust_vc::spec]
fn exec_spec_verified_struct_pred(a: ExecSpecVerifiedA) -> bool {
    a.a > a.b
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_id_u32(x)),
    returns(result),
)]
fn exec_exec_spec_verified_id_u32(x: u32) -> u32 {
    x
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_literal_true()),
    returns(result),
)]
fn exec_exec_spec_verified_literal_true() -> bool {
    true
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_literal_i32()),
    returns(result),
)]
fn exec_exec_spec_verified_literal_i32() -> i32 {
    123i32
}

#[trust_vc::requires(x <= 0xffffu32)]
#[trust_vc::contract(
    ensures(result == exec_spec_verified_square_bounded(x)),
    returns(result),
)]
fn exec_exec_spec_verified_square_bounded(x: u32) -> u32 {
    x * x
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_usize_eq(i, j)),
    returns(result),
)]
fn exec_exec_spec_verified_usize_eq(i: usize, j: usize) -> bool {
    if i == j {
        true
    } else {
        false
    }
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_option_u8_eq(a, b)),
    returns(result),
)]
fn exec_exec_spec_verified_option_u8_eq(a: Option<u8>, b: Option<u8>) -> bool {
    if a == b {
        true
    } else {
        false
    }
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_constant_usize_max_minus(i)),
    returns(result),
)]
fn exec_exec_spec_verified_constant_usize_max_minus(i: usize) -> bool {
    if usize::MAX - i != 0usize {
        true
    } else {
        false
    }
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_pred(a, b)),
    returns(result),
)]
fn exec_exec_spec_verified_pred(a: u32, b: u32) -> bool {
    if a > b {
        true
    } else {
        false
    }
}

#[trust_vc::contract(
    ensures(result == exec_spec_verified_struct_pred(a)),
    returns(result),
)]
fn exec_exec_spec_verified_struct_pred_fails_closed(a: ExecSpecVerifiedA) -> bool {
    a.a > a.b
}

#[trust_vc::ensures(true)]
fn exec_spec_verified_generated_u32_wrapper_caller_fails_closed(x: u32) {
    let y = exec_exec_spec_verified_id_u32(x);
    trust_vc::assert!(y == x);
}

#[trust_vc::requires(a > b)]
#[trust_vc::ensures(true)]
fn exec_spec_verified_generated_pred_wrapper_caller_fails_closed(a: u32, b: u32) {
    let res = exec_exec_spec_verified_pred(a, b);
    trust_vc::assert!(res);
}

#[trust_vc::ensures(true)]
fn exec_exec_spec_verified_literal_i32_wrong_counterexample() {
    let result = 122i32;
    trust_vc::assert!(result == 123i32);
}

#[trust_vc::ensures(true)]
fn exec_exec_spec_verified_square_wrong_counterexample() {
    let square_of_two = 4u32;
    let result = 3u32;
    trust_vc::assert!(result == square_of_two);
}

#[trust_vc::ensures(true)]
fn exec_exec_spec_verified_constant_wrong_counterexample() {
    let i = usize::MAX;
    let result = true;
    let _ = i;
    trust_vc::assert!(!result);
}

#[trust_vc::contract(
    ensures(exec_exec_spec_verified_id_u32(x) == result),
    returns(result),
)]
fn exec_spec_verified_exec_wrapper_in_contract_fails_closed(x: u32) -> u32 {
    x
}
