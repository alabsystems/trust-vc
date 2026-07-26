// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// Partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/loops.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally ports
// only Rust-valid loop behavior TrustVc can model today:
// - while-loop invariant and normal-exit facts;
// - loop facts for unmodified locals across ordinary, nested, and shadowing
//   loop bodies;
// - boolean while normal-exit facts plus current-gap nested-break
//   counterexamples;
// - minimal invariant_except_break / loop_ensures witnesses for break and
//   continue;
// - stable counterexamples for missing loop facts, reachable breaks, and wrong
//   post-loop assertions; and
// - fail-closed boundaries for source-level loop_decreases! and Verus old-state
//   loop reasoning.
//
// Full parity still needs Verus loop-header invariant/decreases syntax,
// loop-havoc diagnostics, richer break/continue flow, ghost/proof code in loop
// guards, iterator loops and `for x in iter:` syntax, subrange via clauses,
// old/final mutable-reference loop reasoning, loop_isolation(false) behavior,
// recursive-call termination inside loops, and exact upstream diagnostic counts.

pub const LOOPS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "basic_while_invariant_establishes_assertion",
        "basic_while",
        "verified",
        3,
    ),
    (
        "while_unmodified_variable_not_havoced_verified",
        "test_variables_not_havoc_basic",
        "verified",
        1,
    ),
    (
        "while_shadowed_variable_no_effect_verified",
        "test_variables_no_effect_basic",
        "verified",
        1,
    ),
    (
        "nested_while_outer_variable_not_havoced_verified",
        "test_variables_not_havoc_nested",
        "verified",
        1,
    ),
    ("while_bool_guard_normal_exit", "while_b", "verified", 3),
    (
        "loop_continue_loop_ensures_post_loop_use",
        "example_loop_continue",
        "verified",
        4,
    ),
    (
        "loop_break_invariant_except_break",
        "example_loop_break",
        "verified",
        4,
    ),
    (
        "loop_break_regular_invariant_preserves_unmodified_fact",
        "basic_loop",
        "verified",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact",
        "loop2_ok_y unmodified-state subset",
        "verified",
        3,
    ),
    (
        "basic_while_missing_upper_invariant_counterexample",
        "basic_while_fail1",
        "counterexample",
        1,
    ),
    (
        "while_nested_inner_break_current_gap_counterexample",
        "while_b2 current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_labeled_inner_break_current_gap_counterexample",
        "while_b2_y current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_break_does_not_assume_normal_exit_counterexample",
        "while_to_loop_break",
        "counterexample",
        1,
    ),
    (
        "while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        "counterexample",
        1,
    ),
    (
        "loop_break_false_counterexample",
        "loop_break_false",
        "counterexample",
        1,
    ),
    (
        "loop_labeled_break_false_counterexample",
        "loop_break_false_y",
        "counterexample",
        1,
    ),
    (
        "loop_nested_break_to_outer_false_counterexample",
        "loop_infinite2x",
        "counterexample",
        1,
    ),
    (
        "loop_break_regular_unmodified_invariant_current_gap_counterexample",
        "basic_loop non-tautological invariant current TrustVc gap",
        "counterexample",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_current_gap_counterexample",
        "loop2_ok_y non-tautological invariant current TrustVc gap",
        "counterexample",
        3,
    ),
    (
        "while_loop_decreases_verified",
        "loop_termination_supported / loop_decreases1 boundary",
        "verified",
        9,
    ),
    (
        "loop_old_state_invariant_boundary_currently_errors",
        "loop_references_old_version_of_mut_var old-state boundary",
        "error",
        0,
    ),
];

pub const LOOPS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "loop_old_state_invariant_boundary_currently_errors",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
];

pub fn loops_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    LOOPS_RS_EXPECTED_CASES
}

pub fn loops_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    LOOPS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn basic_while_invariant_establishes_assertion(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

// Rust-valid slice adjacent to upstream `test_variables_not_havoc_basic`:
// variables not assigned by a break-exiting loop keep their arithmetic facts.
#[trust_vc::requires(a < 100u64)]
#[trust_vc::ensures(true)]
fn while_unmodified_variable_not_havoced_verified(a: u64) {
    let mut i = 0u64;
    let mut j = a;
    j = j + 2u64;

    while i < 1u64 {
        i = i + 1u64;
        if i == 1u64 {
            break;
        }
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Rust-valid slice adjacent to upstream `test_variables_no_effect_basic`: a
// shadowed loop-local variable does not affect the outer variable.
#[trust_vc::ensures(true)]
fn while_shadowed_variable_no_effect_verified() {
    let mut i = 0u64;
    let mut k = 12u64;

    while i < 1u64 {
        let mut k = i;
        i = i + 1u64;
        k = k + 1u64;
        break;
    }

    k = k + 1u64;
    trust_vc::assert!(k == 13u64);
}

// Rust-valid slice adjacent to upstream `test_variables_not_havoc_nested`: a
// nested loop-local shadow does not havoc an outer variable of the same name.
#[trust_vc::requires(a < 100u64)]
#[trust_vc::ensures(true)]
fn nested_while_outer_variable_not_havoced_verified(a: u64) {
    let mut i = 0u64;
    let mut j = a;
    j = j + 2u64;

    while i < 1u64 {
        i = i + 1u64;
        let mut j = 0u64;
        while j < 1u64 {
            j = j + 1u64;
            break;
        }
        break;
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Faithful executable slice of upstream `while_b`: normal exit from a pure
// boolean while loop establishes the negated guard.
#[trust_vc::ensures(true)]
fn while_bool_guard_normal_exit(b: bool) {
    while b {}

    trust_vc::assert!(!b);
}

// Upstream `while_b2` normal-exit fact: the inner unlabeled break exits only
// the inner loop and the outer loop has no break, so `!b` holds on normal
// exit. Historically a TrustVc gap pinned as counterexample; the label-scoped
// break-target analysis now proves it. Flip audited 2026-07-04: assert!(b)
// and break-'outer false twins both still produce counterexamples.
#[trust_vc::ensures(true)]
fn while_nested_inner_break_current_gap_counterexample(b: bool) {
    while b {
        while b {
            break;
        }
    }

    trust_vc::assert!(!b);
}

// Upstream `while_b2_y`: the labeled break exits only the nested loop, so
// `!b` holds on the outer loop's normal exit. Historically a TrustVc gap
// pinned as counterexample; now proven. Flip audited 2026-07-04: assert!(b)
// and break-'outer false twins both still produce counterexamples.
#[trust_vc::ensures(true)]
fn while_labeled_inner_break_current_gap_counterexample(b: bool) {
    while b {
        'y: while b {
            break 'y;
        }
    }

    trust_vc::assert!(!b);
}

// Stable local counterexample adjacent to upstream `basic_while_fail1`: the
// normal-exit fact proves only the lower bound, not the exact final value.
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn basic_while_missing_upper_invariant_counterexample(mut i: u64, limit: u64) {
    while i < limit {
        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

// Faithful executable slice of upstream `while_to_loop_break`: a break out of
// the while body cannot justify the normal-exit guard fact.
#[trust_vc::ensures(true)]
fn while_break_does_not_assume_normal_exit_counterexample(b: bool) {
    while b {
        break;
    }

    trust_vc::assert!(!b);
}

// Faithful executable slice of upstream `while_b2_x`: a labeled break to the
// outer while bypasses the outer normal-exit guard fact.
#[trust_vc::ensures(true)]
fn while_labeled_break_to_outer_counterexample(b: bool) {
    'x: while b {
        while b {
            break 'x;
        }
    }

    trust_vc::assert!(!b);
}

// Minimal supported slice of upstream `example_loop_continue`: a continue path
// does not suppress the loop postcondition fact used after the loop.
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_continue_loop_ensures_post_loop_use(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        trust_vc::loop_ensures!(i >= 10u64);

        i = i + 1u64;
        if i == 5u64 {
            continue;
        }
    }

    trust_vc::assert!(i >= 10u64);
}

// Minimal supported slice of upstream `example_loop_break`: a loop with a break
// may carry an invariant_except_break clause, but that fact is not used as an
// unconditional post-loop assertion.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_invariant_except_break(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        trust_vc::invariant_except_break!(limit == 10u64);
        trust_vc::loop_ensures!(limit == 10u64);

        i = i + 1u64;
        if i == limit {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Faithful executable slice of upstream `loop_break_false`: a normal break from
// a bare loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_break_false_counterexample() {
    loop {
        break;
    }

    trust_vc::assert!(false);
}

// Faithful executable slice of upstream `loop_break_false_y`: an unlabeled
// break from a labeled loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_labeled_break_false_counterexample() {
    'y: loop {
        break;
    }

    trust_vc::assert!(false);
}

// Faithful executable slice of upstream `loop_infinite2x`: a nested break to
// the outer loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_nested_break_to_outer_false_counterexample() {
    'x: loop {
        loop {
            break 'x;
        }
    }

    trust_vc::assert!(false);
}

// Supported slice of upstream `basic_loop` / `loop2_ok`: a bare `loop {}` with
// a `break` carries regular tautological invariant metadata and reaches the
// following assertion. Non-tautological regular invariant facts are pinned below
// as current counterexamples.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_regular_invariant_preserves_unmodified_fact(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(true);

        i = i + 1u64;
        if i == 1u64 {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Supported slice of upstream `loop2_ok_y`: a labeled inner break still carries
// tautological invariant metadata and reaches the following assertion.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(true);

        i = i + 1u64;
        'y: loop {
            trust_vc::invariant!(true);
            break 'y;
        }

        if i == 1u64 {
            break 'x;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Current TrustVc gap adjacent to upstream `basic_loop`: file extraction rejects
// non-tautological regular invariants even when they mention unmodified state.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_regular_unmodified_invariant_current_gap_counterexample(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == 10u64);

        i = i + 1u64;
        if i == 1u64 {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Current TrustVc gap adjacent to upstream `loop2_ok_y`: the labeled inner
// break shape has the same non-tautological regular invariant limitation.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_labeled_inner_break_regular_invariant_current_gap_counterexample(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(limit == 10u64);

        i = i + 1u64;
        'y: loop {
            trust_vc::invariant!(limit == 10u64);
            break 'y;
        }

        if i == 1u64 {
            break 'x;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Source-level loop_decreases! now verifies on the file path: the measure
// `10 - i` strictly decreases each iteration and the precondition establishes
// the invariant at entry (de-surrogated — was a fail-closed boundary).
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn while_loop_decreases_verified(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

// Fail-closed boundary for upstream `loop_references_old_version_of_mut_var`:
// TrustVc does not yet model Verus old-state loop invariants in source files.
#[trust_vc::ensures(true)]
fn loop_old_state_invariant_boundary_currently_errors(mut i: u64) {
    while i < 1u64 {
        trust_vc::invariant!(old(i) == 0u64);
        i = i + 1u64;
    }

    trust_vc::assert!(i >= 1u64);
}
