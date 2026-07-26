// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/summer_school.rs`.
//
// This file intentionally keeps the corpus manifest entry as
// `unsupported-gap`. The upstream Summer School corpus starts with small
// assertion/spec-function lessons, then moves into Verus set, sequence, map,
// enum/module, recursive-fuel, and Vec view examples. TrustVc does not yet
// replace that full teaching corpus.
//
// The Rust-valid scout below records only stable evidence TrustVc can execute
// today:
// - simple assertion and implication lessons from e01/e02;
// - arithmetic spec-function witnesses from e03/e04;
// - a narrow Set membership model adjacent to the e05 set literal lesson; and
// - a small `set!` literal smoke test.
//
// Broader parity remains unsupported: richer Verus `set!`, `seq!`, and `map!`
// literals, extensional equality, set/sequence/map comprehensions, module
// splitting, structural enum reasoning, reveal_with_fuel, recursive decreases,
// Vec view loop invariants, binary search, and exact Verus diagnostic text.

#![allow(dead_code)]

use trust_vc_types::{int, Set};

pub const SUMMER_SCHOOL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("e01_assertion_verified", "e01_pass", "verified", 1),
    (
        "e01_assertion_counterexample",
        "e01_fail",
        "counterexample",
        1,
    ),
    ("e02_implication_verified", "e02_pass", "verified", 1),
    (
        "e02_implication_counterexample",
        "e02_fail",
        "counterexample",
        1,
    ),
    (
        "e03_double_literal_arithmetic_verified",
        "e03_pass",
        "verified",
        1,
    ),
    (
        "e03_double_wrong_literal_counterexample",
        "e03_fail",
        "counterexample",
        1,
    ),
    (
        "e04_four_times_nonnegative_verified",
        "e04_pass",
        "verified",
        1,
    ),
    (
        "e04_four_times_unconstrained_counterexample",
        "e04_fail",
        "counterexample",
        1,
    ),
    (
        "e05_set_membership_model_verified",
        "e05_pass",
        "verified",
        1,
    ),
    (
        "e05_set_membership_false_followup_counterexample",
        "e05_fail",
        "counterexample",
        1,
    ),
    (
        "e05_verus_set_literal_macro_verified",
        "e05_pass",
        "verified",
        1,
    ),
];

pub fn summer_school_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SUMMER_SCHOOL_RS_EXPECTED_CASES
}

#[trust_vc::spec]
fn summer_school_double(val: int) -> int {
    2 * val
}

#[trust_vc::spec]
fn summer_school_at_least_twice_as_big(a: int, b: int) -> bool {
    a >= 2 * b
}

fn e01_assertion_verified() {
    trust_vc::assert!(5i32 > 3i32);
}

fn e01_assertion_counterexample() {
    trust_vc::assert!(5i32 < 3i32);
}

fn e02_implication_verified() {
    trust_vc::assert!(!true || true);
}

fn e02_implication_counterexample() {
    trust_vc::assert!(!true || false);
}

fn e03_double_literal_arithmetic_verified() {
    trust_vc::assert!(summer_school_double(6 as int) == (6 as int) + (6 as int));
    trust_vc::assert!(summer_school_double(-2 as int) == -4 as int);
}

fn e03_double_wrong_literal_counterexample() {
    trust_vc::assert!(summer_school_double(-2 as int) == 4 as int);
}

#[trust_vc::requires(x >= 0)]
fn e04_four_times_nonnegative_verified(x: int) {
    trust_vc::assert!(summer_school_at_least_twice_as_big(
        summer_school_double(summer_school_double(x)),
        x
    ));
}

fn e04_four_times_unconstrained_counterexample(x: int) {
    trust_vc::assert!(summer_school_at_least_twice_as_big(
        summer_school_double(summer_school_double(x)),
        x
    ));
}

fn e05_set_membership_model_verified() {
    trust_vc::assert!(Set::<int>::empty().insert(7 as int).contains(7 as int));
    trust_vc::assert!(!Set::<int>::empty().insert(7 as int).contains(9 as int));
    trust_vc::assert!(Set::<int>::empty()
        .insert(7 as int)
        .insert(6 as int)
        .insert(5 as int)
        .contains(7 as int));
}

fn e05_set_membership_false_followup_counterexample() {
    trust_vc::assert!(Set::<int>::empty().insert(7 as int).contains(7 as int));
    trust_vc::assert!(false);
}

fn e05_verus_set_literal_macro_verified() {
    trust_vc::assert!(set![7].contains(7));
}
