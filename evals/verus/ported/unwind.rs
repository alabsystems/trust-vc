// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/unwind.rs`.
//
// This file intentionally covers only a small Rust-valid contract boundary.
// Upstream Verus checks `no_unwind`, conditional `no_unwind when ...`, invariant
// masks, trait unwind specifications, external-body specifications, closure
// calls, and allocation unwinding diagnostics. TrustVc does not currently expose
// those unwind clauses directly.
//
// This scout slice models the executable precondition boundary behind
// `fn_conditional_unwind(i) no_unwind when i >= 5`, proves callers that
// satisfy it (including a simple no-panic leaf call), rejects one caller that
// does not, and pins upstream-shaped panic/closure-call unwind boundaries as
// fail-closed unsupported behavior.

#![allow(dead_code)]

pub const UNWIND_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test_caller_conditional2_no_unwind_leaf_verified",
        "basic",
        "verified",
        1,
    ),
    (
        "test_caller_conditional3_contract_boundary_verified",
        "basic",
        "verified",
        1,
    ),
    (
        "test_caller_no_unwind3_no_panic_path_verified",
        "basic",
        "verified",
        1,
    ),
    (
        "test_closure2_application_verified",
        "basic",
        "verified",
        1,
    ),
    (
        "test_caller_no_unwind2_contract_boundary_counterexample",
        "basic",
        "counterexample",
        1,
    ),
    (
        "test_caller_conditional4_contract_boundary_counterexample",
        "basic",
        "counterexample",
        1,
    ),
    (
        "test_closure2_application_liar_counterexample",
        "basic",
        "counterexample",
        1,
    ),
    (
        "test_caller_no_unwind1_panic_boundary_currently_errors",
        "basic",
        "error",
        0,
    ),
];

pub const UNWIND_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "test_caller_no_unwind1_panic_boundary_currently_errors",
        &["panic"],
    ),
];

pub fn unwind_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    UNWIND_RS_EXPECTED_CASES
}

pub fn unwind_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    UNWIND_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(i >= 5u8)]
#[trust_vc::ensures(result == i)]
fn trust_vc_conditional_unwind_boundary(i: u8) -> u8 {
    i
}

#[trust_vc::ensures(true)]
fn trust_vc_no_panic_leaf_boundary() {}

#[trust_vc::requires(j >= 10u8)]
#[trust_vc::ensures(true)]
fn test_caller_conditional2_no_unwind_leaf_verified(j: u8) {
    trust_vc_no_panic_leaf_boundary();
    trust_vc::assert!(j >= 10u8);
}

#[trust_vc::requires(j >= 10u8)]
#[trust_vc::ensures(true)]
fn test_caller_conditional3_contract_boundary_verified(j: u8) {
    let observed = trust_vc_conditional_unwind_boundary(j);
    trust_vc::assert!(observed == j);
    trust_vc::assert!(observed >= 5u8);
}

#[trust_vc::ensures(true)]
fn test_caller_no_unwind3_no_panic_path_verified() {
    trust_vc_no_panic_leaf_boundary();
    let observed = trust_vc_conditional_unwind_boundary(20u8);
    trust_vc::assert!(observed == 20u8);
    trust_vc::assert!(observed >= 5u8);
}

#[trust_vc::ensures(true)]
fn test_caller_no_unwind2_contract_boundary_counterexample() {
    let observed = trust_vc_conditional_unwind_boundary(3u8);
    trust_vc::assert!(observed == 3u8);
}

#[trust_vc::requires(j >= 4u8)]
#[trust_vc::ensures(true)]
fn test_caller_conditional4_contract_boundary_counterexample(j: u8) {
    let observed = trust_vc_conditional_unwind_boundary(j);
    trust_vc::assert!(observed == j);
}

#[trust_vc::ensures(true)]
fn test_caller_no_unwind1_panic_boundary_currently_errors() {
    trust_vc_no_panic_leaf_boundary();
    panic!("models an unwind crossing through a no-unwind boundary");
}

#[trust_vc::ensures(true)]
fn test_closure2_application_verified() {
    let f = || 1u8;
    let observed = f();
    trust_vc::assert!(observed == 1u8);
}

// Liar twin (2026-09-11): the zero-argument closure returns 1.
#[trust_vc::ensures(true)]
fn test_closure2_application_liar_counterexample() {
    let f = || 1u8;
    let observed = f();
    trust_vc::assert!(observed == 2u8);
}
