// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_closures.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally ports
// only Rust-valid mutable-reference behavior adjacent to concrete upstream
// closure tests:
// - direct local and parameter-derived `&mut` writes that mirror the body and
//   zero-valued call site of the simple closure-with-mut-ref-argument cases;
// - a first-local mutable borrow adjacent to the returning-mut-ref closure
//   body, because tuple-projected mutable references remain blocked;
// - a stable stale-value counterexample after such a write;
// - a stable false assertion from the mutable-reference-in-closure body; and
// - direct local closure calls, tuple-field mutable borrows,
//   mutable-reference-returning closures, closure call reflection,
//   closure resolvedness, and old/final post-state expressions as fail-closed
//   boundaries.
//
// Full parity still needs Verus closure-local requires/ensures clauses,
// `old`/`final` mutable-reference post-state, `call_requires`/`call_ensures`,
// `has_resolved`, proof closures, `mut_ref_current`, closure capture of mutable
// references, and exact diagnostic parity.

#![allow(dead_code)]

pub const MUT_REFS_CLOSURES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_closure_arg_direct_update_verified",
        "closure_with_mut_ref_arg_basic",
        "verified",
        1,
    ),
    (
        "mut_refs_closure_arg_two_direct_updates_verified",
        "closure_with_mut_ref_arg_basic",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_arg_param_increment_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_in_closure_rebind_body_verified",
        "mut_refs_in_closure",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_returning_first_local_borrow_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_arg_wrong_old_value_counterexample",
        "closure_with_mut_ref_arg_basic",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_arg_param_increment_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_arg_direct_update_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_in_closure_rebind_body_false_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_returning_first_local_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_returning_tuple_field_borrow_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_direct_mut_ref_arg_application_currently_errors",
        "closure_with_mut_ref_arg_basic",
        "error",
        0,
    ),
    (
        "mut_refs_closure_returning_mut_ref_arg_currently_errors",
        "closure_returning_mut_ref_arg_basic",
        "error",
        0,
    ),
    (
        "mut_refs_closure_call_requires_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_call_ensures_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_old_final_post_state_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_has_resolved_capture_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_mut_ref_current_capture_verified",
        "spec_capture_of_mut_ref",
        "verified",
        1,
    ),
    (
        "mut_refs_closure_mut_ref_current_capture_wrong_value_counterexample",
        "spec_capture_of_mut_ref",
        "counterexample",
        1,
    ),
];

pub const MUT_REFS_CLOSURES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "mut_refs_closure_returning_tuple_field_borrow_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
            "tuple/index/nested projections",
        ],
    ),
    (
        "mut_refs_closure_direct_mut_ref_arg_application_currently_errors",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_closure_returning_mut_ref_arg_currently_errors",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_closure_call_requires_currently_errors",
        &[
            "call_requires",
            "unknown return type for function",
            "standalone closure",
            "assignment through a dereferenced reference is unsupported",
        ],
    ),
    (
        "mut_refs_closure_call_ensures_currently_errors",
        &[
            "call_ensures",
            "unknown return type for function",
            "standalone closure",
            "assignment through a dereferenced reference is unsupported",
        ],
    ),
    (
        "mut_refs_closure_old_final_post_state_currently_errors",
        &[
            "Unsupported old-state expression `old(...)`",
            "Failed to parse assert!() expression",
            "final",
            "old",
        ],
    ),
    (
        "mut_refs_closure_has_resolved_capture_currently_errors",
        &["has_resolved", "is refused", "standalone closure"],
    ),
];

pub fn mut_refs_closures_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_CLOSURES_RS_EXPECTED_CASES
}

pub fn mut_refs_closures_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MUT_REFS_CLOSURES_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_direct_update_verified() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_two_direct_updates_verified() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 1u64);

    let mut y = 0u64;
    let y_ref: &mut u64 = &mut y;

    *y_ref = *y_ref + 1u64;

    trust_vc::assert!(y == 1u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_param_increment_verified(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 1u64);
    trust_vc::assert!(*x_ref == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_wrong_old_value_counterexample() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 0u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_param_increment_wrong_value_counterexample(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_arg_direct_update_false_tail_counterexample() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(x == 1u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_in_closure_rebind_body_verified() {
    let mut x = 0u64;
    let mut y = 10u64;

    let mut x_ref = &mut x;
    *x_ref = 20u64;

    trust_vc::assert!(x == 20u64);

    x_ref = &mut y;
    *x_ref = 30u64;

    trust_vc::assert!(y == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_in_closure_rebind_body_false_counterexample() {
    let mut x = 0u64;
    let mut y = 10u64;

    let mut x_ref = &mut x;
    *x_ref = 20u64;

    trust_vc::assert!(x == 20u64);

    x_ref = &mut y;
    *x_ref = 30u64;

    trust_vc::assert!(y == 30u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_returning_first_local_borrow_verified() {
    let mut first_value = 0u64;
    let second_value = 1u64;
    let first: &mut u64 = &mut first_value;

    *first = 10u64;

    trust_vc::assert!(first_value == 10u64);
    trust_vc::assert!(second_value == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_returning_first_local_false_tail_counterexample() {
    let mut first_value = 0u64;
    let second_value = 1u64;
    let first: &mut u64 = &mut first_value;

    *first = 10u64;

    trust_vc::assert!(first_value == 10u64);
    trust_vc::assert!(second_value == 1u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_returning_tuple_field_borrow_currently_errors() {
    let mut x = (0u64, 1u64);
    let fst: &mut u64 = &mut x.0;

    *fst = 10u64;

    trust_vc::assert!(x.0 == 10u64);
    trust_vc::assert!(x.1 == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_direct_mut_ref_arg_application_currently_errors() {
    let c = |a: &mut u64| {
        *a = *a + 1u64;
    };

    let mut x = 0u64;
    c(&mut x);

    trust_vc::assert!(x == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_returning_mut_ref_arg_currently_errors() {
    let c = |pair: &mut (u64, u64)| -> &mut u64 { &mut pair.0 };

    let mut x = (0u64, 1u64);
    *c(&mut x) = 10u64;

    trust_vc::assert!(x.0 == 10u64);
    trust_vc::assert!(x.1 == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_call_requires_currently_errors() {
    let c = |a: &mut u64| {
        *a = *a + 1u64;
    };

    let mut x = 0u64;
    trust_vc::assert!(call_requires(c, (&mut x,)));
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_call_ensures_currently_errors() {
    let c = |a: &mut u64| {
        *a = *a + 1u64;
    };

    let mut x = 0u64;
    trust_vc::assert!(call_ensures(c, (&mut x,), ()));
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_old_final_post_state_currently_errors(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = *x_ref + 1u64;

    trust_vc::assert!(*final(x_ref) == *old(x_ref) + 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_has_resolved_capture_currently_errors() {
    let value = 7u64;
    let clos = || {
        trust_vc::assert!(value == 7u64);
    };

    let _captured = clos;
    trust_vc::assert!(has_resolved(value));
}

// Upstream `spec_capture_of_mut_ref` is `Ok(())`: after `*x = 5` the CURRENT
// value behind the captured `&mut` is 5, and a spec capture may read it. Pinned
// in both directions -- the twin claims the pre-write value and must be refuted.
#[trust_vc::ensures(true)]
fn mut_refs_closure_mut_ref_current_capture_verified(x: &mut u64) {
    *x = 5u64;

    let clos = || {
        trust_vc::assert!(mut_ref_current(x) == 5u64);
    };

    clos();
}

#[trust_vc::ensures(true)]
fn mut_refs_closure_mut_ref_current_capture_wrong_value_counterexample(x: &mut u64) {
    *x = 5u64;

    let clos = || {
        trust_vc::assert!(mut_ref_current(x) == 4u64);
    };

    clos();
}
