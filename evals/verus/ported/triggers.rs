// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/triggers.rs`.
//
// This scout keeps the upstream file as an unsupported gap. It covers only a
// narrow explicit-trigger quantifier surface that TrustVc can currently execute:
// - an arithmetic trigger on a universal arithmetic identity verifies;
// - Verus-style inner trigger groups in assert-forall syntax verify for a
//   small arithmetic identity, including one multi-pattern group;
// - an adjacent false universal produces a concrete rejection;
// - a false explicit-trigger universal remains fail-closed as solver Unknown;
// - a trigger that does not mention the bound variable fails closed.
// - closure-form quantifier-level trigger syntax fails closed.
//
// Broader parity remains unsupported: let-bound trigger terms, Seq/Map trigger
// cases, nonlinear proof blocks, uninterpreted spec-function trigger behavior,
// bitwise triggers, lambda/spec_fn triggers, broadcast/all_triggers behavior,
// clone/self trigger regressions, and Verus diagnostic text.

pub const TRIGGERS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "arithmetic_trigger_quantifier_verified",
        "test_ok_arith_trigger",
        "verified",
        1,
    ),
    (
        "verus_style_multi_trigger_groups_verified",
        "test_multiple_triggers",
        "verified",
        1,
    ),
    (
        "trigger_adjacent_quantifier_counterexample",
        "test_arith_function_trigger_fail",
        "counterexample",
        1,
    ),
    (
        "trigger_without_bound_var_fails_closed",
        "test_fails_single_trigger",
        "error",
        0,
    ),
    (
        "quantifier_level_trigger_syntax_fails_closed",
        "test_multiple_triggers",
        "error",
        0,
    ),
];

pub fn triggers_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    TRIGGERS_RS_EXPECTED_CASES
}

pub const TRIGGERS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "trigger_without_bound_var_fails_closed",
        &["does not reference any bound variable"],
    ),
    (
        "quantifier_level_trigger_syntax_fails_closed",
        &["Failed to parse assert_forall_by!() expression"],
    ),
];

pub fn triggers_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    TRIGGERS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn arithmetic_trigger_quantifier_verified() {
    trust_vc::assert!(forall |i: int| #[trigger] (i + 0) == i);
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn verus_style_multi_trigger_groups_verified() {
    trust_vc::assert_forall_by!(assert forall |i: int, j: int|
        #![trigger (i + j)]
        #![trigger (i + 0), (j + 0)]
        i == i && j == j by {
            trust_vc::assume!(i == i && j == j);
        }
    );
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn trigger_adjacent_quantifier_counterexample() {
    trust_vc::assert!(forall |i: i32| i > 0i32);
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn explicit_trigger_false_universal_currently_unknown() {
    trust_vc::assert!(forall |i: int| #[trigger] (i + 0) == i + 1);
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn trigger_without_bound_var_fails_closed() {
    trust_vc::assert_forall_by!(|i: int| #[trigger] (0 + 1) == 1 && i == i, {
        trust_vc::assume!(i == i);
    });
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn quantifier_level_trigger_syntax_fails_closed() {
    trust_vc::assert_forall_by!(|i: int| #![trigger (i + 0)] i == i, {
        trust_vc::assume!(i == i);
    });
}
