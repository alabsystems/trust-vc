// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/examples.rs`.
//
// Upstream examples.rs is a Verus harness that macro-expands every file under
// the examples directories, reads each example's first-line directive, and then
// checks the verifier process result against a `Mode` predicate. This file keeps
// the corpus entry as `unsupported-gap` and pins only the Rust-valid predicate
// core that TrustVc can verify directly today:
// - selected ExpectSuccess and ExpectFailures acceptance predicates;
// - false acceptance predicates that must not verify; and
// - the examples_in_dir! macro boundary, which remains fail-closed instead of
//   being accepted as replacement evidence for the generated upstream harness.
//
// Full parity remains unsupported: recursive examples_in_dir! expansion,
// filesystem first-line parsing, Verus diagnostic parsing, command-line option
// forwarding, and exact stdout/stderr/report matching are not mirrored here.

#![allow(dead_code, unused_macros)]

pub const EXAMPLES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "examples_expect_success_predicate_verified",
        "run_example_for_file",
        "verified",
        1,
    ),
    (
        "examples_expect_success_with_warning_counterexample",
        "run_example_for_file",
        "counterexample",
        1,
    ),
    (
        "examples_expect_failures_predicate_verified",
        "run_example_for_file",
        "verified",
        1,
    ),
    (
        "examples_expect_failures_without_failures_counterexample",
        "run_example_for_file",
        "counterexample",
        1,
    ),
    (
        "examples_in_dir_macro_expansion_boundary_fail_closed",
        "examples_in_dir",
        "error",
        0,
    ),
];

pub fn examples_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXAMPLES_RS_EXPECTED_CASES
}

pub const EXAMPLES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "examples_in_dir_macro_expansion_boundary_fail_closed",
    &["unsupported expression `macro`"],
)];

pub fn examples_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    EXAMPLES_RS_EXPECTED_ERROR_PATTERNS
}

macro_rules! examples_in_dir {
    ($path:literal) => {
        true
    };
}

#[trust_vc::ensures(true)]
fn examples_expect_success_predicate_verified(
    process_status_success: bool,
    verifier_reported_zero_errors: bool,
    is_internal_failure: bool,
    warnings_are_empty: bool,
) {
    trust_vc::assume!(process_status_success);
    trust_vc::assume!(verifier_reported_zero_errors);
    trust_vc::assume!(!is_internal_failure);
    trust_vc::assume!(warnings_are_empty);

    let accepted = process_status_success
        && verifier_reported_zero_errors
        && !is_internal_failure
        && warnings_are_empty;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn examples_expect_success_with_warning_counterexample(
    process_status_success: bool,
    verifier_reported_zero_errors: bool,
    is_internal_failure: bool,
    warnings_are_empty: bool,
) {
    trust_vc::assume!(process_status_success);
    trust_vc::assume!(verifier_reported_zero_errors);
    trust_vc::assume!(!is_internal_failure);
    trust_vc::assume!(!warnings_are_empty);

    let accepted = process_status_success
        && verifier_reported_zero_errors
        && !is_internal_failure
        && warnings_are_empty;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn examples_expect_failures_predicate_verified(
    process_status_success: bool,
    verifier_reported_failures: bool,
) {
    trust_vc::assume!(!process_status_success);
    trust_vc::assume!(verifier_reported_failures);

    let accepted = !process_status_success && verifier_reported_failures;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn examples_expect_failures_without_failures_counterexample(
    process_status_success: bool,
    verifier_reported_failures: bool,
) {
    trust_vc::assume!(!process_status_success);
    trust_vc::assume!(!verifier_reported_failures);

    let accepted = !process_status_success && verifier_reported_failures;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn examples_in_dir_macro_expansion_boundary_fail_closed() {
    trust_vc::assert!(examples_in_dir!("../../examples"));
}
