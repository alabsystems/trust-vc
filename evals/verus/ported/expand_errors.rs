// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/expand_errors.rs`.
//
// The upstream file validates Verus `--expand-errors` diagnostic expansion for
// failed assertions, requires clauses, ensures clauses, quantified failures,
// opaque reveal scopes, trait-associated specs, and exact rendered diagnostic
// notes. TrustVc does not expose Verus' expanded-error note model, so the
// manifest entry must remain `unsupported-gap`.
//
// This scout records only the narrow predicate-boundary behavior TrustVc can
// express today:
// - a verified caller that satisfies an expanded predicate-shaped helper;
// - counterexamples for a failed assertion plus failed precondition and
//   postcondition obligations with the same concrete predicate shape; and
// - a fail-closed unsupported `expand_errors(...)` metadata clause so Verus
//   diagnostic-expansion annotations cannot be accepted silently.
//
// Full rendered expansion-note parity, span mapping, quantified expansion,
// reveal-flow behavior, trait diagnostic expansion, and uninterpreted/open-spec
// notes remain unsupported here.

use trust_vc_types::int;

pub const EXPAND_ERRORS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "expand_errors_assertion_verified",
        "test1_expand_error",
        "verified",
        2,
    ),
    (
        "expand_errors_assertion_counterexample",
        "test1_expand_error",
        "counterexample",
        2,
    ),
    (
        "expand_errors_requires_counterexample",
        "test3_expand_requires",
        "counterexample",
        2,
    ),
    (
        "expand_errors_ensures_counterexample",
        "test4_expand_ensures",
        "counterexample",
        1,
    ),
    (
        "expand_errors_metadata_fails_closed",
        "test1_expand_error",
        "error",
        0,
    ),
];

pub fn expand_errors_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXPAND_ERRORS_RS_EXPECTED_CASES
}

pub const EXPAND_ERRORS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "expand_errors_metadata_fails_closed",
    &["unknown contract clause `expand_errors` in #[contract]"],
)];

pub fn expand_errors_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    EXPAND_ERRORS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::spec]
fn expand_errors_is_good_integer(z: int) -> bool {
    z >= 0 && z != 5
}

#[trust_vc::ensures(true)]
fn expand_errors_assertion_verified() {
    let x = 4;
    trust_vc::assert!(expand_errors_is_good_integer(x));
}

#[trust_vc::ensures(true)]
fn expand_errors_assertion_counterexample() {
    let x = 5;
    trust_vc::assert!(expand_errors_is_good_integer(x));
}

#[trust_vc::requires(x >= 0 && x != 5)]
#[trust_vc::ensures(true)]
fn expand_errors_requires_boundary(x: int) {
    let _ = x;
}

#[trust_vc::ensures(true)]
fn expand_errors_requires_counterexample() {
    expand_errors_requires_boundary(5);
}

#[trust_vc::returns(result)]
#[trust_vc::ensures(result >= 0 && result != 5)]
fn expand_errors_ensures_counterexample() -> int {
    5
}

#[trust_vc::contract(expand_errors(expand_errors_is_good_integer), ensures(true))]
fn expand_errors_metadata_fails_closed() {
    trust_vc::assert!(true);
}
