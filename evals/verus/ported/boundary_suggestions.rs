// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/boundary_suggestions.rs`.
//
// The upstream file checks Verus diagnostics and suggested declarations for
// `assume_specification` and `external_type_specification`. TrustVc does not
// currently emit those Verus suggestion strings or accept the proxy declaration
// syntax. This scout file therefore keeps the upstream manifest entry as an
// unsupported-gap and records only a Rust-valid adjacent contract boundary:
// - an external/trusted function with an explicit TrustVc contract can be used
//   by a verified caller;
// - multiple external/trusted boundary contracts can be used together by a
//   verified caller;
// - callers still must satisfy the boundary precondition;
// - callers cannot prove facts that contradict the trusted postcondition; and
// - an executable helper used from a specification clause fails closed instead
//   of being accepted as an implicit assume-specification suggestion.
//
// Broader parity remains unsupported: Verus help text, generic/lifetime/const
// generic suggestion formatting, self/foreign assume_specification suggestions,
// format! visibility suggestions, external_type_specification proxy syntax, and
// recursive-type rejection annotations are not claimed here.

pub const BOUNDARY_SUGGESTIONS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "boundary_suggestion_assume_spec_contract_verified",
        "test_assume_specification_simple_suggestion_correct",
        "verified",
        1,
    ),
    (
        "boundary_suggestion_two_contracts_verified",
        "test_two_assume_specification_suggestions_made / corrected trusted boundary contracts",
        "verified",
        1,
    ),
    (
        "boundary_suggestion_requires_violation_counterexample",
        "test_assume_specification_simple_suggestion_correct",
        "counterexample",
        1,
    ),
    (
        "boundary_suggestion_two_contracts_requires_violation_counterexample",
        "test_two_assume_specification_suggestions_made / missing one trusted boundary precondition",
        "counterexample",
        1,
    ),
    (
        "boundary_suggestion_trusted_postcondition_counterexample",
        "test_assume_specification_simple_suggestion_correct",
        "counterexample",
        1,
    ),
    (
        "boundary_suggestion_two_contracts_postcondition_counterexample",
        "test_two_assume_specification_suggestions_made / contradictory trusted boundary postconditions",
        "counterexample",
        1,
    ),
    (
        "boundary_suggestion_helper_spec_term_fails_closed",
        "test_assume_specification_simple_suggestion_made",
        "error",
        0,
    ),
];

pub fn boundary_suggestions_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    BOUNDARY_SUGGESTIONS_RS_EXPECTED_CASES
}

pub const BOUNDARY_SUGGESTIONS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "boundary_suggestion_helper_spec_term_fails_closed",
    &["Unsupported call to sibling helper"],
)];

pub fn boundary_suggestions_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    BOUNDARY_SUGGESTIONS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::external]
#[trust_vc::contract(
    requires(boundary_guard),
    ensures(result == !flag),
    returns(result),
)]
fn boundary_suggestion_trusted_negate(flag: bool, boundary_guard: bool) -> bool {
    let _ = boundary_guard;
    !flag
}

#[trust_vc::external]
#[trust_vc::contract(
    requires(boundary_guard),
    ensures(result == true),
    returns(result),
)]
fn boundary_suggestion_trusted_true(boundary_guard: bool) -> bool {
    let _ = boundary_guard;
    true
}

#[trust_vc::external]
#[trust_vc::contract(
    requires(boundary_guard),
    ensures(result == false),
    returns(result),
)]
fn boundary_suggestion_trusted_false(boundary_guard: bool) -> bool {
    let _ = boundary_guard;
    false
}

#[trust_vc::ensures(true)]
fn boundary_suggestion_assume_spec_contract_verified() {
    let observed = boundary_suggestion_trusted_negate(true, true);
    trust_vc::assert!(observed == false);
}

#[trust_vc::requires(boundary_guard)]
#[trust_vc::ensures(true)]
fn boundary_suggestion_two_contracts_verified(boundary_guard: bool) {
    let observed_true = boundary_suggestion_trusted_true(boundary_guard);
    let observed_false = boundary_suggestion_trusted_false(boundary_guard);
    trust_vc::assert!(observed_true);
    trust_vc::assert!(!observed_false);
}

#[trust_vc::ensures(true)]
fn boundary_suggestion_requires_violation_counterexample() {
    let _ = boundary_suggestion_trusted_negate(true, false);
}

#[trust_vc::ensures(true)]
fn boundary_suggestion_two_contracts_requires_violation_counterexample() {
    let _ = boundary_suggestion_trusted_true(false);
}

#[trust_vc::ensures(true)]
fn boundary_suggestion_trusted_postcondition_counterexample() {
    let observed = boundary_suggestion_trusted_negate(false, true);
    trust_vc::assert!(observed == false);
}

#[trust_vc::ensures(true)]
fn boundary_suggestion_two_contracts_postcondition_counterexample() {
    let observed_true = boundary_suggestion_trusted_true(true);
    let observed_false = boundary_suggestion_trusted_false(true);
    trust_vc::assert!(observed_true == observed_false);
}

#[trust_vc::contract(
    ensures(boundary_suggestion_trusted_negate(flag, boundary_guard) == result),
    returns(result),
)]
fn boundary_suggestion_helper_spec_term_fails_closed(flag: bool, boundary_guard: bool) -> bool {
    let _ = boundary_guard;
    !flag
}
