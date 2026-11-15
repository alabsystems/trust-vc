// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/exec_termination.rs`.
//
// This is not accepted replacement evidence. It only pins a small Rust-valid
// subset around recursive decreases, multi-call and lexicographic recursion,
// loop safety facts adjacent to missing-decreases upstream cases, upstream
// loop-clause shapes, and fail-closed loop-decreases/mutual-recursion
// boundaries.
// Full upstream parity still requires executable-recursion termination
// diagnostics, missing-decreases rejection, mutual recursion, Verus loop
// clauses, option-gated nontermination, trait flags, assume_termination, and
// exact diagnostic behavior.

#![allow(dead_code)]

use trust_vc_types::nat;

pub const EXEC_TERMINATION_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "recursive_exec_function_with_decreases_clause_small_compute_verified",
        "recursive_exec_function_with_decreases_clause",
        "verified",
        1,
    ),
    (
        "recursive_exec_function_with_decreases_clause_wrong_value_counterexample",
        "recursive_exec_function_with_decreases_clause",
        "counterexample",
        1,
    ),
    (
        "recursive_exec_function_with_two_decreasing_calls_small_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "recursive_exec_function_with_two_decreasing_calls_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "loop_with_break_with_decreases_clause_verified",
        "loop_with_break_with_decreases_clause",
        "verified",
        8,
    ),
];

// De-surrogated: file-path loop_decreases! now routes. The break-loop case is a
// counterexample (moved out of the error group); the for-loop case stays an
// error (unresolvable induction variable) but is checked only via the regression
// suite's FAIL_CLOSED_CASES, not this metadata array.
pub const EXEC_TERMINATION_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[];

pub fn exec_termination_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXEC_TERMINATION_RS_EXPECTED_CASES
}

pub fn exec_termination_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    EXEC_TERMINATION_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn exec_termination_recursive_identity(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        1 + exec_termination_recursive_identity((i - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_decreases_clause_small_compute_verified() {
    trust_vc::assert_by_compute!(
        exec_termination_recursive_identity(5 as nat) == (5 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_decreases_clause_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        exec_termination_recursive_identity(5 as nat) == (6 as nat);
        compute_only
    );
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn exec_termination_recursive_fibonacci(i: nat) -> nat {
    if i == 0 {
        0
    } else if i == 1 {
        1
    } else {
        exec_termination_recursive_fibonacci((i - 1) as nat)
            + exec_termination_recursive_fibonacci((i - 2) as nat)
    }
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_two_decreasing_calls_small_compute_verified() {
    trust_vc::assert_by_compute!(
        exec_termination_recursive_fibonacci(6 as nat) == (8 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_two_decreasing_calls_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        exec_termination_recursive_fibonacci(6 as nat) == (9 as nat);
        compute_only
    );
}

#[trust_vc::decreases(outer, inner)]
#[trust_vc::spec]
fn exec_termination_lexicographic_countdown(outer: nat, inner: nat) -> nat {
    if inner > 0 {
        1 + exec_termination_lexicographic_countdown(outer, (inner - 1) as nat)
    } else if outer > 0 {
        1 + exec_termination_lexicographic_countdown((outer - 1) as nat, 2 as nat)
    } else {
        0
    }
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_lexicographic_decreases_small_compute_verified() {
    trust_vc::assert_by_compute!(
        exec_termination_lexicographic_countdown(2 as nat, 1 as nat) == (7 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn recursive_exec_function_with_lexicographic_decreases_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        exec_termination_lexicographic_countdown(2 as nat, 1 as nat) == (8 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn while_loop_missing_decreases_safety_shape_verified(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(true);

        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

#[trust_vc::ensures(true)]
fn while_loop_missing_decreases_wrong_exit_fact_counterexample(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(true);

        i = i + 1u64;
    }

    trust_vc::assert!(i < 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_with_break_loop_clause_safety_shape_verified(mut i: u64, limit: u64) {
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

// Upstream `loop_with_break_with_decreases_clause` (Verus: Ok). Since 2026-09-10
// (audit rows 430/431) a break-only `if cond { break; }` keeps the body in the
// exact-transition lane: the measure `10 - i` is registered (WF1 under the
// invariant, WF2 under `guard ∧ ¬cond` with the exact `i + 1` transition), the
// invariant is checked at the break site, and the loop VERIFIES — previously
// pinned as an under-verifying Counterexample ("trust-vc under-verifies a loop
// Verus accepts"). `requires(i <= 10)` establishes the invariant at entry.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn loop_with_break_with_decreases_clause_verified(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(i <= 10u64);
}

// For-loop over a bounded range: the range `for` now desugars to the equivalent
// counter-driven `while` (for_range_desugar.rs), so the loop is REASONED about
// rather than fail-closed. The invariant `i <= 30` is NOT established at entry —
// `i` is an unconstrained `u64` parameter (no `#[requires]`), so establishment
// can pick `i = u64::MAX > 30` — and the loop invariant check COUNTEREXAMPLEs.
// (Verus rejects the same shape: an invariant over an unconstrained parameter is
// not established.) This is the sound boundary: Error → Counterexample, both
// "not verified".
#[trust_vc::ensures(true)]
fn for_loop_with_decreases_clause_boundary_counterexample(mut i: u64) {
    for x in 0u64..10u64 {
        trust_vc::invariant!(i <= 30u64);
        trust_vc::loop_decreases!(10u64 - x);

        i = i + 3u64;
    }

    trust_vc::assert!(i <= 30u64);
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn exec_termination_mutual_even(i: nat) -> bool {
    if i == 0 {
        true
    } else {
        exec_termination_mutual_odd((i - 1) as nat)
    }
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn exec_termination_mutual_odd(i: nat) -> bool {
    if i == 0 {
        false
    } else {
        exec_termination_mutual_even((i - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn mutually_recursive_exec_functions_with_decreases_currently_fail_closed() {
    trust_vc::assert_by_compute!(exec_termination_mutual_even(4 as nat); compute_only);
}
