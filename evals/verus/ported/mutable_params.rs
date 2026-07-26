// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream mutable_params.rs.
//
// This file covers only Rust-valid mutable-parameter shapes adjacent to the
// upstream direct mutable-parameter groups. Closure contracts, loop-return
// extraction, full loop isolation semantics, invariant-mask interactions,
// unwind specs, recommends checking over mutable parameters, and exact
// diagnostics remain unsupported. The decreases surrogate is pinned separately
// as a semantic blocker because TrustVc currently verifies it instead of
// rejecting it as Verus does.

#![allow(dead_code)]

use trust_vc_types::int;

pub const MUTABLE_PARAMS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mutable_param_return_original_verified",
        "mut_param_with_loops::test",
        "verified",
        1,
    ),
    (
        "mutable_param_explicit_return_original_verified",
        "mut_param_with_loops::test explicit Rust return",
        "verified",
        1,
    ),
    (
        "mutable_param_iso_false_return_original_verified",
        "mut_param_with_loops_iso_false::test",
        "verified",
        1,
    ),
    (
        "mutable_param_conditional_snapshot_original_verified",
        "mutation_conditional_cases direct conditional snapshot subset",
        "verified",
        1,
    ),
    (
        "mutable_param_return_mutated_counterexample",
        "mut_param_with_loops::test_fails",
        "counterexample",
        1,
    ),
    (
        "mutable_param_iso_false_return_mutated_counterexample",
        "mut_param_with_loops_iso_false::test_fails",
        "counterexample",
        1,
    ),
    (
        "mutable_param_preloop_assignment_return_current_counterexample",
        "mut_param_with_loops::test_loop_fails2 direct pre-loop assignment subset",
        "counterexample",
        1,
    ),
    (
        "mutable_param_loop_return_currently_errors",
        "mut_param_with_loops::test_loop",
        "error",
        0,
    ),
    (
        "mutable_param_loop_snapshot_then_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails0",
        "error",
        0,
    ),
    (
        "mutable_param_loop_return_mutated_currently_errors",
        "mut_param_with_loops::test_loop_fails",
        "error",
        0,
    ),
    (
        "mutable_param_loop_preloop_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails2",
        "error",
        0,
    ),
    (
        "mutable_param_loop_conditional_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails3",
        "error",
        0,
    ),
    (
        "mutable_param_iso_false_loop_return_currently_errors",
        "mut_param_with_loops_iso_false::test_loop",
        "error",
        0,
    ),
    (
        "mutable_param_closure_application_currently_errors",
        "mut_param_on_closure_with_loops::test",
        "error",
        0,
    ),
    (
        "mutable_param_closure_mutated_application_currently_errors",
        "mut_param_on_closure_with_loops::test_fails",
        "error",
        0,
    ),
    (
        "mutable_param_iso_false_closure_application_currently_errors",
        "mut_param_on_closure_with_loops_iso_false::test",
        "error",
        0,
    ),
    (
        "mutable_param_open_atomic_invariant_boundary_currently_errors",
        "no_confusion_invariants_spec::open",
        "error",
        0,
    ),
    (
        "mutable_param_unwind_panic_boundary_currently_errors",
        "no_confusion_unwind_spec::open",
        "error",
        0,
    ),
    (
        "mutable_param_decreases_clause_currently_verifies_blocker",
        "no_confusion_decreases_clause::test",
        "verified-blocker",
        0,
    ),
    (
        "mutable_param_conditional_mutated_return_counterexample",
        "mutation_conditional_cases::test5 direct conditional mutation subset",
        "counterexample",
        1,
    ),
    (
        "mutable_param_nested_mutation_before_return_counterexample",
        "mutation_nested_loop direct nested mutation subset",
        "counterexample",
        1,
    ),
    // Re-pinned 2026-07-04 (was "unknown"): the engine now refutes the
    // unsatisfiable postcondition (spec fn body is `false`) with a genuine
    // Counterexample; recommends semantics remain unmodeled, so this stays a
    // non-evidence blocker status.
    (
        "mutable_param_ensures_recommends_currently_unknown",
        "no_confusion_ensures_recommend_check::test_ens",
        "counterexample-blocker",
        1,
    ),
];

pub fn mutable_params_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUTABLE_PARAMS_RS_EXPECTED_CASES
}

#[trust_vc::ensures(result == x)]
fn mutable_param_return_original_verified(mut x: u64) -> u64 {
    let z = x;
    x = 5u64;
    let _ = x;
    z
}

#[trust_vc::ensures(result == x)]
fn mutable_param_explicit_return_original_verified(mut x: u64) -> u64 {
    let z = x;
    x = 5u64;
    let _ = x;
    return z;
}

#[trust_vc::ensures(result == x)]
fn mutable_param_iso_false_return_original_verified(mut x: u64) -> u64 {
    let z = x;
    x = 5u64;
    let _ = x;
    z
}

#[trust_vc::ensures(result == x)]
fn mutable_param_conditional_snapshot_original_verified(mut x: u64, choose_left: bool) -> u64 {
    let z = x;
    if choose_left {
        x = 20u64;
    } else {
        x = 30u64;
    }
    let _ = x;
    z
}

#[trust_vc::ensures(result == x)]
fn mutable_param_return_mutated_counterexample(mut x: u64) -> u64 {
    x = 5u64;
    let _ = x;
    5u64
}

#[trust_vc::ensures(result == x)]
fn mutable_param_iso_false_return_mutated_counterexample(mut x: u64) -> u64 {
    x = 5u64;
    let _ = x;
    5u64
}

#[trust_vc::ensures(result == x)]
fn mutable_param_preloop_assignment_return_current_counterexample(mut x: u64) -> u64 {
    x = 1u64;
    let z = x;
    z
}

#[trust_vc::ensures(result == x)]
fn mutable_param_conditional_mutated_return_counterexample(
    mut x: u64,
    mutate: bool,
) -> u64 {
    if mutate {
        x = 20u64;
    } else {
        x = 20u64;
    }
    x
}

#[trust_vc::ensures(result == x)]
fn mutable_param_nested_mutation_before_return_counterexample(
    mut x: u64,
    outer: bool,
    inner: bool,
) -> u64 {
    if outer {
        if inner {
            x = 20u64;
        } else {
            x = 20u64;
        }
    } else {
        x = 20u64;
    }
    x
}

#[trust_vc::spec]
#[trust_vc::recommends(x == 2)]
fn mutable_params_rec(x: int) -> bool {
    false
}

#[trust_vc::ensures(mutable_params_rec(x))]
fn mutable_param_ensures_recommends_currently_unknown(mut x: int) {
    x = 2;
    let _ = x;
}

#[trust_vc::ensures(result == x)]
fn mutable_param_loop_return_currently_errors(mut x: u64) -> u64 {
    loop {
        return x;
    }
}

#[trust_vc::ensures(result == x)]
fn mutable_param_loop_snapshot_then_mutation_return_currently_errors(mut x: u64) -> u64 {
    loop {
        let z = x;
        x = 5u64;
        let _ = x;
        return z;
    }
}

#[trust_vc::ensures(result == x)]
fn mutable_param_loop_return_mutated_currently_errors(mut x: u64) -> u64 {
    loop {
        x = 5u64;
        return 5u64;
    }
}

#[trust_vc::ensures(result == x)]
fn mutable_param_loop_preloop_mutation_return_currently_errors(mut x: u64) -> u64 {
    x = 1u64;
    loop {
        let z = x;
        return z;
    }
}

#[trust_vc::ensures(result == x)]
fn mutable_param_loop_conditional_mutation_return_currently_errors(
    mut x: u64,
    choose_return: bool,
) -> u64 {
    loop {
        if choose_return {
            let z = x;
            return z;
        } else {
            x = 1u64;
        }
    }
}

#[trust_vc::ensures(result == x)]
fn mutable_param_iso_false_loop_return_currently_errors(mut x: u64) -> u64 {
    loop {
        return x;
    }
}

#[trust_vc::ensures(true)]
fn mutable_param_open_atomic_invariant_boundary_currently_errors(mut x: u64) {
    x = 1u64;
    let _ = x;

    open_atomic_invariant!(x => i => {});
}

#[trust_vc::ensures(true)]
fn mutable_param_unwind_panic_boundary_currently_errors(mut x: u64) {
    x = 1u64;
    let _ = x;

    panic!("models a panic crossing a no_unwind boundary");
}

#[allow(unconditional_recursion)]
#[trust_vc::decreases(x)]
#[trust_vc::ensures(true)]
fn mutable_param_decreases_clause_currently_verifies_blocker(mut x: u64) {
    x = 30u64;
    let _ = x;

    mutable_param_decreases_clause_currently_verifies_blocker(20u64);
}

#[trust_vc::ensures(true)]
fn mutable_param_closure_application_currently_errors() {
    let f = |mut x: u64| -> u64 {
        let z = x;
        x = 5u64;
        let _ = x;
        z
    };

    trust_vc::assert!(f(10u64) == 10u64);
}

#[trust_vc::ensures(true)]
fn mutable_param_closure_mutated_application_currently_errors() {
    let f = |mut x: u64| -> u64 {
        x = 5u64;
        let _ = x;
        5u64
    };

    trust_vc::assert!(f(10u64) == 10u64);
}

#[trust_vc::ensures(true)]
fn mutable_param_iso_false_closure_application_currently_errors() {
    let f = |mut x: u64| -> u64 {
        let z = x;
        x = 5u64;
        let _ = x;
        z
    };

    trust_vc::assert!(f(10u64) == 10u64);
}
