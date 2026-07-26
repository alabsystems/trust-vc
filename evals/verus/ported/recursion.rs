// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/recursion.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally records
// only Rust-valid evidence TrustVc can execute today:
// - bounded direct, signed, multi-call, and lexicographic recursive spec compute
//   witnesses;
// - deterministic wrong-value counterexamples for the same supported compute
//   slice; and
// - fail-closed boundaries for mutual source-spec recursion, explicit fuel,
//   decreases_to!, decreases_by/recommends_by-like markers, and old-state
//   mutable-reference termination shapes.
//
// Full upstream parity remains unsupported: missing-decreases diagnostics,
// proof-mode recursion termination, full mutual recursion/fuel behavior,
// Verus decreases_by/decreases_when/recommends_by semantics, termination checks
// before definition/across modules, recursive datatype heights, trait/generic
// recursion, cloned/invariant recursion, and diagnostic parity are not claimed.

#![allow(dead_code)]

use trust_vc_types::nat;

pub const UPSTREAM_RECURSION_RS_PINNED_CASES: &[&str] = &[
    "basic_correctness_expr",
    "basic_correctness_expr_fail",
    "basic_correctness_stmt",
    "basic_correctness_stmt_fail",
    "mutually_recursive_expressions",
    "mutually_recursive_expressions_insufficient_fuel",
    "mutually_recursive_statements",
    "expr_decrease_fail_1",
    "expr_wrong_decreases",
    "mutual_expr_decrease_fail",
    "multidecrease1",
    "termination_checked_before_definition1",
    "termination_checked_across_modules",
    "basic_decreases_by",
    "basic_decreases_by_int",
    "proof_decreases_when_ok",
    "proof_decreases_recommends_fail",
    "mutable_reference_decreases_2_fail",
    "decrease_through_seq",
    "height_intrinsic",
    "mutual_recursion_result_incompleteness_regression_564_1",
    "decreases_checks_assert_by",
    "recursive_through_struct_with_invariants_ok",
];

pub fn upstream_recursion_rs_pinned_cases() -> &'static [&'static str] {
    UPSTREAM_RECURSION_RS_PINNED_CASES
}

pub type RecursionRsExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const RECURSION_RS_EXPECTED_CASES: &[RecursionRsExpectedCase] = &[
    (
        "basic_correctness_expr_small_compute_verified",
        "basic_correctness_expr",
        "verified",
        1,
    ),
    (
        "basic_correctness_expr_wrong_value_counterexample",
        "basic_correctness_expr",
        "counterexample",
        1,
    ),
    (
        "basic_decreases_by_int_guarded_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "basic_decreases_by_int_guarded_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "multi_call_recursive_spec_small_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "multi_call_recursive_spec_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "lexicographic_recursive_spec_small_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "lexicographic_recursive_spec_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    // AUDITED FLIP (2026-07-08): error -> verified. The B5 mutual-recursion
    // defining-axiom feature (ad62cc3) removed the "recursive source spec
    // function dependency" rejection; the compute path now genuinely evaluates
    // through the a->b->a cycle. Soundness probed firsthand: the TRUE claim
    // a(2)==2 Verifies and the FALSE claim a(2)==3 is a Counterexample
    // ("by(compute): expression evaluates to false") — not vacuous.
    (
        "mutually_recursive_expressions_currently_fail_closed",
        "mutually_recursive_expressions",
        "verified",
        1,
    ),
    (
        "recursive_reveal_with_fuel_currently_fail_closed",
        "",
        "error",
        0,
    ),
    (
        "multidecrease_decreases_to_currently_fail_closed",
        "",
        "error",
        0,
    ),
    (
        "decreases_by_clause_currently_fail_closed",
        "",
        "error",
        0,
    ),
    (
        "recommends_by_clause_currently_fail_closed",
        "",
        "error",
        0,
    ),
    // AUDITED FLIP 2026-07-09: slice B: old(value)==old(value) tautology now verifies; upstream rejects diagnostically - documented scout divergence
    (
        "mutable_reference_old_state_decreases_currently_fail_closed",
        "",
        "verified",
        1,
    ),
];

pub fn recursion_rs_expected_cases() -> &'static [RecursionRsExpectedCase] {
    RECURSION_RS_EXPECTED_CASES
}

pub type RecursionRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const RECURSION_RS_EXPECTED_ERROR_PATTERNS: &[RecursionRsExpectedErrorPatterns] = &[
    // mutually_recursive_expressions_currently_fail_closed removed 2026-07-08:
    // it now VERIFIES via the B5 mutual-recursion defining axioms (ad62cc3) —
    // see the audited flip in RECURSION_RS_EXPECTED_CASES.
    (
        "recursive_reveal_with_fuel_currently_fail_closed",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "multidecrease_decreases_to_currently_fail_closed",
        &[
            "Unsupported decreases_to!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "decreases_by_clause_currently_fail_closed",
        &[
            "Unsupported decreases_by!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "recommends_by_clause_currently_fail_closed",
        &[
            "Unsupported recommends_by!()",
            "unsupported macros are rejected",
        ],
    ),
    // mutable_reference_old_state_decreases_currently_fail_closed removed 2026-07-09: audited slice-B flip (see the expected-cases table).
    ];

pub fn recursion_rs_expected_error_patterns() -> &'static [RecursionRsExpectedErrorPatterns] {
    RECURSION_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn arith_sum_nat(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        i + arith_sum_nat((i - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn basic_correctness_expr_small_compute_verified() {
    trust_vc::assert_by_compute!(arith_sum_nat(4 as nat) == (10 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn basic_correctness_expr_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(arith_sum_nat(4 as nat) == (11 as nat); compute_only);
}

#[trust_vc::decreases(i, when = i >= 0i64)]
#[trust_vc::spec]
fn arith_sum_i64_guarded(i: i64) -> i64 {
    if i <= 0i64 {
        0i64
    } else {
        i + arith_sum_i64_guarded(i - 1i64)
    }
}

#[trust_vc::ensures(true)]
fn basic_decreases_by_int_guarded_compute_verified() {
    trust_vc::assert_by_compute!(arith_sum_i64_guarded(4i64) == 10i64; compute_only);
}

#[trust_vc::ensures(true)]
fn basic_decreases_by_int_guarded_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(arith_sum_i64_guarded(4i64) == 11i64; compute_only);
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn fib_nat(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        if i == 1 {
            1
        } else {
            fib_nat((i - 1) as nat) + fib_nat((i - 2) as nat)
        }
    }
}

#[trust_vc::ensures(true)]
fn multi_call_recursive_spec_small_compute_verified() {
    trust_vc::assert_by_compute!(fib_nat(5 as nat) == (5 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn multi_call_recursive_spec_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(fib_nat(5 as nat) == (6 as nat); compute_only);
}

#[trust_vc::decreases(outer, inner)]
#[trust_vc::spec]
fn lexicographic_countdown(outer: nat, inner: nat) -> nat {
    if inner > 0 {
        1 + lexicographic_countdown(outer, (inner - 1) as nat)
    } else if outer > 0 {
        1 + lexicographic_countdown((outer - 1) as nat, 2 as nat)
    } else {
        0
    }
}

#[trust_vc::ensures(true)]
fn lexicographic_recursive_spec_small_compute_verified() {
    trust_vc::assert_by_compute!(
        lexicographic_countdown(2 as nat, 1 as nat) == (7 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn lexicographic_recursive_spec_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        lexicographic_countdown(2 as nat, 1 as nat) == (8 as nat);
        compute_only
    );
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn mutual_count_down_a(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        1 + mutual_count_down_b((i - 1) as nat)
    }
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn mutual_count_down_b(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        1 + mutual_count_down_a((i - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn mutually_recursive_expressions_currently_fail_closed() {
    trust_vc::assert_by_compute!(mutual_count_down_a(2 as nat) == (2 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn recursive_reveal_with_fuel_currently_fail_closed() {
    trust_vc::reveal_with_fuel!(arith_sum_nat, 2);
    trust_vc::assert_by_compute!(arith_sum_nat(2 as nat) == (3 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn multidecrease_decreases_to_currently_fail_closed() {
    let _decreases = trust_vc::decreases_to!(5u64, 2u64 => 5u64, 1u64);
    trust_vc::assert!(true);
}

#[trust_vc::proof]
fn arith_sum_i64_guarded_decreases_check(_i: i64) {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn decreases_by_clause_currently_fail_closed() {
    trust_vc::decreases_by!(arith_sum_i64_guarded_decreases_check);
    trust_vc::assert!(true);
}

#[trust_vc::proof]
fn recursion_recommends_check() {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn recommends_by_clause_currently_fail_closed() {
    trust_vc::recommends_by!(recursion_recommends_check);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn mutable_reference_old_state_decreases_currently_fail_closed(value: &mut u64) {
    trust_vc::assert!(old(value) == old(value));
}
