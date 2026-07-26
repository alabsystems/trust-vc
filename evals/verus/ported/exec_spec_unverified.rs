// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc port for upstream exec_spec_unverified.rs.
//
// The upstream file exercises the Verus `exec_spec_unverified!` macro, which
// emits executable wrappers for specification functions without proving the
// macro body itself. TrustVc has no direct macro equivalent, so this file covers
// Rust-valid surfaces from `test_exec_spec_unverified_spec`,
// `test_exec_spec_unverified_multivar_quant`, and
// `test_exec_spec_unverified_char_quant`: source spec functions plus manually
// written executable wrappers whose postconditions state that they return the
// spec value.
//
// Full parity remains unsupported: the macro expansion, Verus trigger syntax,
// Verus chained quantifier-bound syntax, nested Seq indexing in generated
// surfaces, mixed exec_spec_verified!/exec_spec_unverified! generated Exec*
// datatypes, and exact Verus diagnostics are outside this slice.

#![allow(dead_code)]

pub type ExecSpecUnverifiedExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const EXEC_SPEC_UNVERIFIED_RS_EXPECTED_CASES: &[ExecSpecUnverifiedExpectedCase] = &[
    (
        "exec_exec_spec_unverified_test2",
        "test_exec_spec_unverified_spec_test2",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_unverified_five",
        "test_exec_spec_unverified_multivar_quant_spec_five",
        "verified",
        1,
    ),
    (
        "exec_spec_unverified_five_exists_concrete_witness_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_unverified_test2_wrong_counterexample",
        "test_exec_spec_unverified_spec_test2_wrong",
        "counterexample",
        1,
    ),
    (
        "exec_exec_spec_unverified_five_wrong_counterexample",
        "test_exec_spec_unverified_multivar_quant_spec_five_wrong",
        "counterexample",
        1,
    ),
    (
        "exec_spec_unverified_five_forall_concrete_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_spec_unverified_five_exists_negated_concrete_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_spec_unverified_generated_wrapper_caller_fails_closed",
        "test_exec_spec_unverified_spec_generated_wrapper_call",
        "verified",
        1,
    ),
    (
        "exec_spec_unverified_exec_wrapper_in_contract_fails_closed",
        "test_exec_spec_unverified_generated_exec_helper_as_spec_term",
        "error",
        0,
    ),
];

pub type ExecSpecUnverifiedFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const EXEC_SPEC_UNVERIFIED_RS_FAIL_CLOSED_ERROR_PATTERNS:
    &[ExecSpecUnverifiedFailClosedErrorPatterns] = &[
    (
        "exec_spec_unverified_exec_wrapper_in_contract_fails_closed",
        &["Unsupported call to sibling helper"],
    ),
];

pub fn exec_spec_unverified_rs_expected_cases() -> &'static [ExecSpecUnverifiedExpectedCase] {
    EXEC_SPEC_UNVERIFIED_RS_EXPECTED_CASES
}

pub fn exec_spec_unverified_rs_fail_closed_error_patterns(
) -> &'static [ExecSpecUnverifiedFailClosedErrorPatterns] {
    EXEC_SPEC_UNVERIFIED_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::spec]
fn exec_spec_unverified_test2() -> bool {
    true
}

#[trust_vc::spec]
fn exec_spec_unverified_five(x1: u8, x2: u8, x3: u8, x4: u8, x5: u8) -> bool {
    (x1 == x2) && (x3 != x4) && (x3 != x5) && (x5 != x2)
}

#[trust_vc::contract(
    ensures(result == exec_spec_unverified_test2()),
    returns(result),
)]
fn exec_exec_spec_unverified_test2() -> bool {
    true
}

#[trust_vc::contract(
    ensures(result == exec_spec_unverified_test2()),
    returns(result),
)]
fn exec_exec_spec_unverified_test2_wrong_counterexample() -> bool {
    false
}

#[trust_vc::contract(
    ensures(result == exec_spec_unverified_five(x1, x2, x3, x4, x5)),
    returns(result),
)]
fn exec_exec_spec_unverified_five(x1: u8, x2: u8, x3: u8, x4: u8, x5: u8) -> bool {
    (x1 == x2) && (x3 != x4) && (x3 != x5) && (x5 != x2)
}

fn exec_spec_unverified_five_exists_concrete_witness_verified() {
    let x1 = 1u8;
    let x2 = 1u8;
    let x3 = 2u8;
    let x4 = 3u8;
    let x5 = 4u8;
    trust_vc::assert!(x1 < 10u8);
    trust_vc::assert!(x2 < 10u8);
    trust_vc::assert!(x3 < 10u8);
    trust_vc::assert!(x4 < 10u8);
    trust_vc::assert!(x5 < 10u8);
    trust_vc::assert!((x1 == x2) && (x3 != x4) && (x3 != x5) && (x5 != x2));
}

fn exec_spec_unverified_five_forall_concrete_counterexample() {
    trust_vc::assert!((0u8 == 0u8) && (0u8 != 0u8) && (0u8 != 0u8) && (0u8 != 0u8));
}

fn exec_spec_unverified_five_exists_negated_concrete_counterexample() {
    trust_vc::assert!(!((1u8 == 1u8) && (2u8 != 3u8) && (2u8 != 4u8) && (4u8 != 1u8)));
}

#[trust_vc::contract(
    ensures(result == exec_spec_unverified_five(x1, x2, x3, x4, x5)),
    returns(result),
)]
fn exec_exec_spec_unverified_five_wrong_counterexample(
    x1: u8,
    x2: u8,
    x3: u8,
    x4: u8,
    x5: u8,
) -> bool {
    (x1 == x2)
}

#[trust_vc::ensures(true)]
fn exec_spec_unverified_generated_wrapper_caller_fails_closed() {
    let res = exec_exec_spec_unverified_test2();
    trust_vc::assert!(res);
}

#[trust_vc::contract(
    ensures(exec_exec_spec_unverified_test2() == result),
    returns(result),
)]
fn exec_spec_unverified_exec_wrapper_in_contract_fails_closed() -> bool {
    true
}
