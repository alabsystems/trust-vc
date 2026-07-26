// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream
// external_fn_specification.rs.
//
// This covers the smallest Rust-valid external-function contract shape from
// upstream `test_basics`: an ignored/external function receives a trusted
// specification, callers prove facts from its postcondition, and bad
// precondition or postcondition uses are rejected. It also pins a direct
// returns-clause boundary and a file-local external_spec! declaration for the
// concrete `u8::default` foreign-trait case. Broader Verus
// external_fn_specification surfaces such as std::mem::swap old/final mutable
// reference contracts, duplicate specs, proxy-call diagnostics, visibility
// checks, associated methods, foreign traits, const assume_specification, and
// when_used_as_spec remain unsupported here.

pub const EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "external_fn_spec_same_crate_call_verified",
        "test_basics::test1",
        "verified",
        1,
    ),
    (
        "external_fn_spec_same_crate_requires_forwarded_verified",
        "test_basics::test1 caller precondition forwarding",
        "verified",
        1,
    ),
    (
        "external_fn_spec_returns_clause_verified",
        "test_allow_in_spec returns-clause contract surrogate",
        "verified",
        1,
    ),
    (
        "external_fn_spec_requires_violation_counterexample",
        "test_basics::test2",
        "counterexample",
        1,
    ),
    (
        "external_fn_spec_postcondition_use_counterexample",
        "test_basics::test3",
        "counterexample",
        1,
    ),
    (
        "external_fn_spec_returns_clause_counterexample",
        "test_allow_in_spec wrong returns-clause use",
        "counterexample",
        1,
    ),
    (
        "external_fn_spec_proxy_contract_call_fails_closed",
        "test_call_proxy / proxy specification surface",
        "error",
        0,
    ),
];

pub fn external_fn_specification_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_CASES
}

pub const EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "external_fn_spec_proxy_contract_call_fails_closed",
    &["Unsupported call to sibling helper"],
)];

pub fn external_fn_specification_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_ERROR_PATTERNS
}

trust_vc::external_spec! {
    impl u8 {
        #[ensures(result == 0u8)]
        fn default() -> u8;
    }
}

#[trust_vc::external]
#[trust_vc::contract(
    requires(x != 0u8),
    ensures(result == !b),
    returns(result),
)]
fn external_fn_spec_negate_bool(b: bool, x: u8) -> bool {
    let _ = x;
    !b
}

#[trust_vc::ensures(true)]
fn external_fn_spec_same_crate_call_verified() {
    let ret_b = external_fn_spec_negate_bool(true, 1u8);
    trust_vc::assert!(ret_b == false);
}

#[trust_vc::requires(x != 0u8)]
#[trust_vc::ensures(true)]
fn external_fn_spec_same_crate_requires_forwarded_verified(x: u8) {
    let ret_b = external_fn_spec_negate_bool(false, x);
    trust_vc::assert!(ret_b == true);
}

#[trust_vc::external]
#[trust_vc::returns(!flag)]
fn external_fn_spec_returns_negation(flag: bool) -> bool {
    !flag
}

#[trust_vc::ensures(true)]
fn external_fn_spec_returns_clause_verified() {
    let observed = external_fn_spec_returns_negation(true);
    trust_vc::assert!(observed == false);
}

#[trust_vc::ensures(true)]
fn external_fn_spec_requires_violation_counterexample() {
    let _ = external_fn_spec_negate_bool(true, 0u8);
}

#[trust_vc::ensures(true)]
fn external_fn_spec_postcondition_use_counterexample() {
    let ret_b = external_fn_spec_negate_bool(true, 1u8);
    trust_vc::assert!(ret_b == true);
}

#[trust_vc::ensures(true)]
fn external_fn_spec_returns_clause_counterexample() {
    let observed = external_fn_spec_returns_negation(true);
    trust_vc::assert!(observed == true);
}

#[trust_vc::contract(
    ensures(external_fn_spec_negate_bool(b, x) == result),
    returns(result),
)]
fn external_fn_spec_proxy_contract_call_fails_closed(b: bool, x: u8) -> bool {
    external_fn_spec_negate_bool(b, x)
}
