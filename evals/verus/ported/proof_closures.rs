// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/proof_closures.rs`.
//
// This file intentionally keeps the coverage narrow. The verified and
// counterexample cases express the same proof-mode pre/post reasoning as the
// simplest upstream `proof_fn` closures through ordinary TrustVc proof-function
// contracts, because direct source-level proof closure calls still fail closed
// below. The one-, two-, and zero-argument witnesses cover basic proof closure
// contract shapes, the helper-call witnesses pin the call pre/post obligations
// that TrustVc can express without claiming support for proof closure syntax,
// and the assignment-call surrogate mirrors the upstream proof-call result
// tracking case with direct proof-function calls.
//
// Full upstream parity still requires proof_fn closure syntax,
// `f.requires`/`f.ensures` reflection, direct proof closure calls, tracked
// closure bindings, ProofFn/ProofFnOnce/ProofFnMut parameter passing, closure
// calls in spec expressions, tracked argument and return modes, mutable-capture
// diagnostics, lifetime/copy/send/sync diagnostics, and exact diagnostic
// parity.

#![allow(dead_code)]

pub type ProofClosuresRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ProofClosuresRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const PROOF_CLOSURES_RS_EXPECTED_CASES: &[ProofClosuresRsExpectedCase] = &[
    (
        "proof_closure_one_arg_contract_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "proof_closure_two_arg_contract_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "proof_closure_zero_arg_return_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_closure_identity_call_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_closure_helper_application_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "proof_closure_calls_in_assignment_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_closure_one_arg_bad_ensures_counterexample",
        "test_ensures_fail",
        "counterexample",
        1,
    ),
    (
        "proof_closure_two_arg_bad_ensures_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_closure_zero_arg_bad_ensures_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_closure_helper_bad_call_requires_counterexample",
        "test_call_requires_fail",
        "counterexample",
        1,
    ),
    (
        "proof_closure_helper_bad_call_ensures_counterexample",
        "test_call_ensures_fail",
        "counterexample",
        1,
    ),
    (
        "proof_closure_calls_in_assignment_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_closure_local_application_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "proof_closure_zero_arg_local_application_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "proof_closure_move_capture_application_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "proof_closure_mut_capture_application_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "proof_closure_call_as_subexpression_currently_errors",
        "",
        "error",
        0,
    ),
];

pub const PROOF_CLOSURES_RS_EXPECTED_ERROR_PATTERNS: &[ProofClosuresRsExpectedErrorPatterns] = &[
    (
        "proof_closure_local_application_currently_errors",
        &["unknown return type for function 'f'", "standalone closure"],
    ),
    (
        "proof_closure_zero_arg_local_application_currently_errors",
        &["unknown return type for function 'f'", "standalone closure"],
    ),
    (
        "proof_closure_move_capture_application_currently_errors",
        &[
            "unknown return type for function 'f'",
            "standalone closure",
            "closure",
        ],
    ),
    (
        "proof_closure_mut_capture_application_currently_errors",
        &[
            "unknown return type for function 'f'",
            "standalone closure",
            "assignment",
            "closure",
        ],
    ),
    (
        "proof_closure_call_as_subexpression_currently_errors",
        &[
            "unknown return type for function 'f'",
            "standalone closure",
            "call function",
            "closure",
        ],
    ),
];

pub fn proof_closures_rs_expected_cases() -> &'static [ProofClosuresRsExpectedCase] {
    PROOF_CLOSURES_RS_EXPECTED_CASES
}

pub fn proof_closures_rs_expected_error_patterns() -> &'static [ProofClosuresRsExpectedErrorPatterns]
{
    PROOF_CLOSURES_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 2u64),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_one_arg_contract_verified(y: u64) -> u64 {
    y
}

#[trust_vc::contract(
    requires(lhs == rhs),
    ensures(z == rhs),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_two_arg_contract_verified(lhs: u64, rhs: u64) -> u64 {
    lhs
}

#[trust_vc::contract(
    ensures(z == 5u64),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_zero_arg_return_contract_verified() -> u64 {
    5u64
}

#[trust_vc::contract(
    ensures(z == i),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_identity_call_contract_verified(i: u64) -> u64 {
    i
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == y),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_call_contract_helper(y: u64) -> u64 {
    y
}

#[trust_vc::proof]
fn proof_closure_helper_application_verified() {
    let observed: u64 = proof_closure_call_contract_helper(2u64);
    trust_vc::assert!(observed == 2u64);
}

#[trust_vc::proof]
fn proof_closure_calls_in_assignment_verified() {
    let mut observed: u64 = proof_closure_identity_call_contract_verified(5u64);
    trust_vc::assert!(observed == 5u64);

    observed = proof_closure_identity_call_contract_verified(7u64);
    trust_vc::assert!(observed == 7u64);
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 3u64),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_one_arg_bad_ensures_counterexample(y: u64) -> u64 {
    y
}

#[trust_vc::contract(
    requires(lhs == rhs),
    ensures(z == lhs),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_two_arg_bad_ensures_counterexample(lhs: u64, rhs: u64) -> u64 {
    lhs + 1u64
}

#[trust_vc::contract(
    ensures(z == 6u64),
    returns(z),
)]
#[trust_vc::proof]
fn proof_closure_zero_arg_bad_ensures_counterexample() -> u64 {
    5u64
}

#[trust_vc::proof]
fn proof_closure_helper_bad_call_requires_counterexample() {
    let _ = proof_closure_call_contract_helper(3u64);
}

#[trust_vc::proof]
fn proof_closure_helper_bad_call_ensures_counterexample() {
    let observed: u64 = proof_closure_call_contract_helper(2u64);
    trust_vc::assert!(observed == 3u64);
}

#[trust_vc::proof]
fn proof_closure_calls_in_assignment_false_tail_counterexample() {
    let mut observed: u64 = proof_closure_identity_call_contract_verified(5u64);
    trust_vc::assert!(observed == 5u64);

    observed = proof_closure_identity_call_contract_verified(7u64);
    trust_vc::assert!(observed == 7u64);
    trust_vc::assert!(false);
}

fn proof_closure_local_application_currently_errors() {
    let f = |y: u64| -> u64 { y };
    trust_vc::assert!(f(2u64) == 2u64);
}

fn proof_closure_zero_arg_local_application_currently_errors() {
    let f = || -> u64 { 5u64 };
    trust_vc::assert!(f() == 5u64);
}

fn proof_closure_move_capture_application_currently_errors(value: u64) {
    let f = move |y: u64| -> u64 { y + value };
    trust_vc::assert!(f(2u64) == value + 2u64);
}

fn proof_closure_mut_capture_application_currently_errors() {
    let mut value = 5u64;
    let mut f = |next: u64| -> u64 {
        value = next;
        value
    };

    trust_vc::assert!(f(7u64) == 7u64);
}

#[trust_vc::proof]
fn proof_closure_requires_twenty(i: u64) {
    trust_vc::assert!(i == 20u64);
}

fn proof_closure_call_as_subexpression_currently_errors() {
    let f = |i: u64| -> u64 { i };
    trust_vc::assert!(f(20u64) == 20u64);
}
