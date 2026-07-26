// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/when_used_as_spec.rs`.
//
// The upstream file exercises `#[verifier::when_used_as_spec]`, where an exec
// function is interpreted as a separate spec function in specification
// positions, plus `#[verifier::allow_in_spec]`, where an exec function may be
// called directly from specs. TrustVc now supports a narrow
// `#[trust_vc::allow_in_spec]` marker for sibling executable helpers with
// explicit contracts, plus a narrow `#[trust_vc::when_used_as_spec(spec_fn)]`
// marker for direct target-contract specification terms. This file records
// explicit spec helpers, executable contracts over those helpers, propagated
// helper-call postconditions, monomorphic allow-in-spec branch surrogates,
// direct allow-in-spec calls in target contracts, direct when-used-as-spec
// target-contract calls, and fail-closed rejection for unmarked executable
// helpers or executable-value contexts.
//
// Full parity remains unsupported: method/trait when_used_as_spec,
// executable-value/runtime context splitting, generic allow-in-spec arbitrary
// values, Verus diagnostics, visibility checks, and &mut-parameter rejection
// are not claimed here.

pub type WhenUsedAsSpecRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type WhenUsedAsSpecRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const WHEN_USED_AS_SPEC_RS_EXPECTED_CASES: &[WhenUsedAsSpecRsExpectedCase] = &[
    (
        "when_used_as_spec_contract_call_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "allow_in_spec_contract_call_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "allow_in_spec_select_u64_contract_surface",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_exec_body_counterexample",
        "fail_exec_false",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_select_u64_false_branch_counterexample",
        "allow_in_spec",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_negate_body_counterexample",
        "allow_in_spec",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_direct_exec_spec_term_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "allow_in_spec_select_u64_direct_exec_spec_term_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_direct_exec_spec_term_fails_closed",
        "test1",
        "error",
        0,
    ),
    (
        "when_used_as_spec_direct_exec_spec_term_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_exec_value_context_fails_closed",
        "fail_exec_false",
        "error",
        0,
    ),
];

pub const WHEN_USED_AS_SPEC_RS_EXPECTED_ERROR_PATTERNS: &[WhenUsedAsSpecRsExpectedErrorPatterns] =
    &[
        (
            "when_used_as_spec_direct_exec_spec_term_fails_closed",
            &["Unsupported call to sibling helper"],
        ),
        (
            "when_used_as_spec_exec_value_context_fails_closed",
            &["unknown return type for function 'when_used_as_spec_direct_exec_helper'"],
        ),
    ];

pub fn when_used_as_spec_rs_expected_cases() -> &'static [WhenUsedAsSpecRsExpectedCase] {
    WHEN_USED_AS_SPEC_RS_EXPECTED_CASES
}

pub fn when_used_as_spec_rs_expected_error_patterns(
) -> &'static [WhenUsedAsSpecRsExpectedErrorPatterns] {
    WHEN_USED_AS_SPEC_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::spec]
fn when_used_as_spec_truth() -> bool {
    true
}

#[trust_vc::contract(
    ensures(result == when_used_as_spec_truth()),
    returns(result),
)]
fn when_used_as_spec_contract_surface() -> bool {
    true
}

#[trust_vc::contract(ensures(true), returns(result))]
fn when_used_as_spec_contract_call_verified() {
    let _observed = when_used_as_spec_contract_surface();
    trust_vc::assert!(_observed);
    trust_vc::assert!(_observed == when_used_as_spec_truth());
}

#[trust_vc::contract(
    ensures(result == when_used_as_spec_truth()),
    returns(result),
)]
fn when_used_as_spec_exec_body_counterexample() -> bool {
    false
}

#[trust_vc::spec]
fn when_used_as_spec_direct_spec_target() -> bool {
    true
}

#[trust_vc::when_used_as_spec(when_used_as_spec_direct_spec_target)]
fn when_used_as_spec_direct_exec_helper() -> bool {
    false
}

#[trust_vc::contract(
    ensures(when_used_as_spec_direct_exec_helper() == result),
    returns(result),
)]
fn when_used_as_spec_direct_exec_spec_term_verified() -> bool {
    true
}

#[trust_vc::contract(ensures(true), returns(result))]
fn when_used_as_spec_exec_value_context_fails_closed() {
    let _observed = when_used_as_spec_direct_exec_helper();
    trust_vc::assert!(_observed);
}

#[trust_vc::contract(
    ensures(when_used_as_spec_contract_surface() == result),
    returns(result),
)]
fn when_used_as_spec_direct_exec_spec_term_fails_closed() -> bool {
    true
}

#[trust_vc::contract(
    ensures(result == !input),
    returns(result),
)]
#[trust_vc::allow_in_spec]
fn allow_in_spec_negate_contract_surface(input: bool) -> bool {
    !input
}

#[trust_vc::contract(requires(input), ensures(true), returns(result))]
fn allow_in_spec_contract_call_verified(input: bool) {
    let _observed = allow_in_spec_negate_contract_surface(input);
    trust_vc::assert!(_observed == false);
}

#[trust_vc::contract(
    requires(input),
    ensures(result == !input),
    returns(result),
)]
fn allow_in_spec_negate_body_counterexample(input: bool) -> bool {
    input
}

#[trust_vc::contract(
    ensures(allow_in_spec_negate_contract_surface(input) == result),
    returns(result),
)]
fn allow_in_spec_direct_exec_spec_term_verified(input: bool) -> bool {
    !input
}

#[trust_vc::spec]
fn allow_in_spec_select_u64_spec(flag: bool, chosen: u64, fallback: u64) -> u64 {
    if flag {
        chosen
    } else {
        fallback
    }
}

#[trust_vc::contract(
    ensures(result == allow_in_spec_select_u64_spec(flag, chosen, fallback)),
    returns(result),
)]
#[trust_vc::allow_in_spec]
fn allow_in_spec_select_u64_contract_surface(flag: bool, chosen: u64, fallback: u64) -> u64 {
    if flag {
        chosen
    } else {
        fallback
    }
}

#[trust_vc::contract(
    requires(!flag),
    ensures(result == allow_in_spec_select_u64_spec(flag, chosen, fallback)),
    returns(result),
)]
fn allow_in_spec_select_u64_false_branch_counterexample(
    flag: bool,
    chosen: u64,
    fallback: u64,
) -> u64 {
    let _ = fallback;
    chosen
}

#[trust_vc::contract(
    ensures(allow_in_spec_select_u64_contract_surface(flag, chosen, fallback) == result),
    returns(result),
)]
fn allow_in_spec_select_u64_direct_exec_spec_term_verified(
    flag: bool,
    chosen: u64,
    fallback: u64,
) -> u64 {
    if flag {
        chosen
    } else {
        fallback
    }
}
