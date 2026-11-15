// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/contrib.rs`.
//
// The upstream file exercises `vstd::contrib::auto_spec`, which makes selected
// executable functions usable from specification/proof contexts. TrustVc has no
// direct `auto_spec` equivalent, so this file records the smallest comparable
// Rust-valid surface: manual spec helpers, executable wrappers whose contracts
// state that they return those spec values, bad wrapper bodies that must not
// verify, one helper-chain witness comparable to the upstream `f2(x) == f(x, 1)`
// case, and fail-closed boundaries for using the executable helper as a spec
// term and for mutable-reference mutation.
//
// This is scout coverage only. The manifest entry remains `unsupported-gap`
// because Verus auto-generated spec functions, proof lemmas over executable
// functions, method auto_spec, auto-import diagnostics, and exact
// `allow_in_spec` diagnostics are not replacement evidence here.

#![allow(dead_code)]

use trust_vc_types::int;

pub type ContribRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ContribRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CONTRIB_RS_EXPECTED_CASES: &[ContribRsExpectedCase] = &[
    (
        "contrib_auto_spec_manual_contract_verified",
        "test_auto_spec::f manual generated-spec wrapper",
        "verified",
        1,
    ),
    (
        "contrib_auto_spec_u32_add_fixup_verified",
        "test_auto_spec::f u32 add generated-spec wrapper",
        "verified",
        1,
    ),
    (
        "contrib_auto_spec_helper_chain_verified",
        "test_auto_spec::f2 generated helper chain",
        "verified",
        1,
    ),
    (
        "contrib_auto_spec_manual_contract_counterexample",
        "test_auto_spec false generated-spec wrapper body",
        "counterexample",
        1,
    ),
    (
        "contrib_auto_spec_helper_chain_counterexample",
        "test_auto_spec false generated helper-chain body",
        "counterexample",
        1,
    ),
    (
        "contrib_auto_spec_exec_call_in_contract_fails_closed",
        "test_auto_spec executable auto_spec function used as spec term",
        "error",
        0,
    ),
    (
        "contrib_auto_spec_mut_ref_body_fails_closed",
        "test_auto_spec_unsupported_body",
        "error",
        0,
    ),
];

pub const CONTRIB_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ContribRsFailClosedErrorPatterns] = &[
    (
        "contrib_auto_spec_exec_call_in_contract_fails_closed",
        &["Unsupported call to sibling helper"],
    ),
    (
        "contrib_auto_spec_mut_ref_body_fails_closed",
        &["dereference expressions are not supported in verification syntax"],
    ),
];

pub fn contrib_rs_expected_cases() -> &'static [ContribRsExpectedCase] {
    CONTRIB_RS_EXPECTED_CASES
}

pub fn contrib_rs_fail_closed_error_patterns() -> &'static [ContribRsFailClosedErrorPatterns] {
    CONTRIB_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::spec]
fn contrib_auto_spec_sum_spec(x: int, y: int) -> int {
    x + y
}

#[trust_vc::contract(
    requires(0 <= x && x < 100 && 0 <= y && y < 100),
    ensures(result == contrib_auto_spec_sum_spec(x, y)),
    returns(result),
)]
fn contrib_auto_spec_manual_contract_verified(x: int, y: int) -> int {
    x + y
}

#[trust_vc::contract(
    requires(0 <= x && x < 100 && 0 <= y && y < 100),
    ensures(result == contrib_auto_spec_sum_spec(x, y)),
    returns(result),
)]
fn contrib_auto_spec_manual_contract_counterexample(x: int, y: int) -> int {
    let _ = y;
    x
}

#[trust_vc::spec]
fn contrib_auto_spec_sum_u32_spec(x: u32, y: u32) -> u32 {
    x + y
}

#[trust_vc::spec]
fn contrib_auto_spec_f2_chain_spec(x: u32) -> u32 {
    contrib_auto_spec_sum_u32_spec(x, 1u32)
}

#[trust_vc::contract(
    requires(x < 100u32 && y < 100u32),
    ensures(result == contrib_auto_spec_sum_u32_spec(x, y)),
    returns(result),
)]
fn contrib_auto_spec_u32_add_fixup_verified(x: u32, y: u32) -> u32 {
    x + y
}

#[trust_vc::contract(
    requires(x < 100u32),
    ensures(result == contrib_auto_spec_f2_chain_spec(x)),
    returns(result),
)]
fn contrib_auto_spec_helper_chain_verified(x: u32) -> u32 {
    x + 1u32
}

#[trust_vc::contract(
    requires(x < 100u32),
    ensures(result == contrib_auto_spec_f2_chain_spec(x)),
    returns(result),
)]
fn contrib_auto_spec_helper_chain_counterexample(x: u32) -> u32 {
    x
}

#[trust_vc::contract(
    ensures(contrib_auto_spec_manual_contract_verified(x, y) == result),
    returns(result),
)]
fn contrib_auto_spec_exec_call_in_contract_fails_closed(x: int, y: int) -> int {
    x + y
}

#[trust_vc::requires(*x < 100u64 && y < 100u64)]
#[trust_vc::ensures(true)]
fn contrib_auto_spec_mut_ref_body_fails_closed(x: &mut u64, y: u64) {
    *x = *x + y;
    trust_vc::assert!(*x >= y);
}
