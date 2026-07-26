// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// Expanded partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/output_json.rs`.
//
// The upstream file validates Verus `--output-json` diagnostic metadata for
// proof notes and custom errors on requires, ensures, asserts, and no-cheating
// assumptions. TrustVc has a different reporting surface and does not currently
// expose the Verus JSON schema or those metadata annotations. This scout slice
// therefore keeps the upstream manifest entry as `unsupported-gap` and records
// only the adjacent Rust-valid contract/report behavior TrustVc can express:
// - verified callers and postconditions satisfying requires/ensures boundaries;
// - rejected first/second precondition, postcondition, assertion, and custom-error
//   shaped obligations;
// - fail-closed output-json/custom-error/no-cheating diagnostic metadata clauses
//   so unsupported annotations cannot be accepted silently; and
// - an assumptions-only no-cheating-adjacent boundary that stays Error, not
//   Verified or Unknown replacement evidence.
//
// Full Verus proof-note/custom-error JSON parity, no-cheating assumption
// reporting, per-function JSON detail sets, and exact diagnostic text remain
// unsupported here.

use trust_vc_types::int;

pub type OutputJsonExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const OUTPUT_JSON_RS_EXPECTED_CASES: &[OutputJsonExpectedCase] = &[
    (
        "output_json_requires_ensures_report_verified",
        "test_json_proof_note_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_two_ensures_report_verified",
        "test_json_proof_note_on_ensures",
        "verified",
        3,
    ),
    (
        "output_json_custom_error_requires_report_verified",
        "test_json_custom_err_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_custom_error_ensures_report_verified",
        "test_json_custom_err_on_ensures",
        "verified",
        1,
    ),
    (
        "output_json_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_second_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        2,
    ),
    (
        "output_json_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_two_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        2,
    ),
    (
        "output_json_custom_error_requires_obligation_counterexample",
        "test_json_custom_err_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_ensures_obligation_counterexample",
        "test_json_custom_err_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_assert_obligation_counterexample",
        "test_json_proof_note_on_assert",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_assert_obligation_counterexample",
        "test_json_custom_err_on_assert",
        "counterexample",
        1,
    ),
    (
        "output_json_no_cheating_assume_only_boundary_errors",
        "test_json_proof_note_on_assume_with_no_cheating",
        "error",
        1,
    ),
    (
        "output_json_proof_note_metadata_fails_closed",
        "test_json_proof_note_on_assert",
        "error",
        0,
    ),
    (
        "output_json_custom_error_metadata_fails_closed",
        "test_json_custom_err_on_assert",
        "error",
        0,
    ),
    (
        "output_json_no_cheating_metadata_fails_closed",
        "test_json_proof_note_on_assume_and_req_with_no_cheating",
        "error",
        0,
    ),
    (
        "output_json_custom_error_no_cheating_metadata_fails_closed",
        "test_json_custom_err_on_assume_with_no_cheating",
        "error",
        0,
    ),
];

pub fn output_json_rs_expected_cases() -> &'static [OutputJsonExpectedCase] {
    OUTPUT_JSON_RS_EXPECTED_CASES
}

pub const OUTPUT_JSON_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "output_json_proof_note_metadata_fails_closed",
        &["unknown contract clause `output_json` in #[contract]"],
    ),
    (
        "output_json_custom_error_metadata_fails_closed",
        &["unknown contract clause `custom_err` in #[contract]"],
    ),
    (
        "output_json_no_cheating_metadata_fails_closed",
        &["unknown contract clause `no_cheating` in #[contract]"],
    ),
    (
        "output_json_custom_error_no_cheating_metadata_fails_closed",
        &["unknown contract clause `no_cheating` in #[contract]"],
    ),
];

pub fn output_json_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    OUTPUT_JSON_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(x == y)]
#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
fn output_json_report_example(x: int, y: int) -> int {
    x + y
}

#[trust_vc::requires(x == y)]
#[trust_vc::requires(x != y)]
#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
fn output_json_two_requires_report_example(x: int, y: int) -> int {
    x + y
}

#[trust_vc::requires(y == 0)]
#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
#[trust_vc::ensures(result == x - y)]
fn output_json_two_ensures_report_example_value(x: int, y: int) -> int {
    x
}

#[trust_vc::ensures(true)]
fn output_json_requires_ensures_report_verified() {
    let observed = output_json_report_example(3, 3);
    trust_vc::assert!(observed == 6);
}

#[trust_vc::ensures(true)]
fn output_json_two_ensures_report_verified() {
    let observed = output_json_two_ensures_report_example_value(9, 0);
    trust_vc::assert!(observed == 9);
}

#[trust_vc::ensures(true)]
fn output_json_custom_error_requires_report_verified() {
    let observed = output_json_report_example(8, 8);
    trust_vc::assert!(observed == 16);
}

#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
fn output_json_custom_error_ensures_report_verified(x: int, y: int) -> int {
    x + y
}

#[trust_vc::ensures(true)]
fn output_json_requires_obligation_counterexample() {
    let _ = output_json_report_example(1, 2);
}

#[trust_vc::ensures(true)]
fn output_json_second_requires_obligation_counterexample() {
    let _ = output_json_two_requires_report_example(3, 3);
}

#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
fn output_json_ensures_obligation_counterexample(x: int, y: int) -> int {
    let _ = y;
    x
}

#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
#[trust_vc::ensures(result == x - y)]
fn output_json_two_ensures_obligation_counterexample(x: int, y: int) -> int {
    let _ = y;
    x
}

#[trust_vc::ensures(true)]
fn output_json_custom_error_requires_obligation_counterexample() {
    let _ = output_json_report_example(10, 11);
}

#[trust_vc::returns(result)]
#[trust_vc::ensures(result == x + y)]
fn output_json_custom_error_ensures_obligation_counterexample(x: int, y: int) -> int {
    let _ = y;
    x
}

#[trust_vc::ensures(true)]
fn output_json_assert_obligation_counterexample() {
    trust_vc::assert!(1 > 2);
}

#[trust_vc::ensures(true)]
fn output_json_custom_error_assert_obligation_counterexample() {
    trust_vc::assert!(1 > 2);
}

fn output_json_no_cheating_assume_only_boundary_errors() {
    trust_vc::assume!(1 > 2);
}

#[trust_vc::contract(output_json(proof_note("Property 732")), ensures(true))]
fn output_json_proof_note_metadata_fails_closed() {
    trust_vc::assert!(true);
}

#[trust_vc::contract(custom_err("Custom assert error"), ensures(true))]
fn output_json_custom_error_metadata_fails_closed() {
    trust_vc::assert!(true);
}

#[trust_vc::contract(no_cheating(output_json), ensures(true))]
fn output_json_no_cheating_metadata_fails_closed() {
    trust_vc::assert!(true);
}

#[trust_vc::contract(no_cheating(custom_err("Custom assume error")), ensures(true))]
fn output_json_custom_error_no_cheating_metadata_fails_closed() {
    trust_vc::assert!(true);
}
