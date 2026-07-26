// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs.rs`.
//
// The upstream file is a broad `new-mut-ref` suite: direct local borrows,
// field borrows, mutable references stored inside values, reborrows,
// prophetic `future`/`final`/`after_borrow` state, resolvedness axioms,
// parameters/returns, two-phase borrows, evaluation order, and exact
// diagnostics.
//
// This scout keeps the manifest row as `unsupported-gap` and records only
// stable Rust-valid TrustVc evidence available today:
// - direct local mutable-reference writes and reads;
// - one-level named-field writes and field-borrow writes;
// - copying from behind a mutable reference, including a value-copy helper;
// - direct nested-alias reassignment between locals;
// - branch-sensitive local writes through a mutable reference;
// - parameter mutable-reference writes through a local alias; and
// - stale-value counterexamples for local, helper-read, alias reassignment, and
//   branch-sensitive writes.
// Fail-closed expected cases pin unsupported boundaries for reborrow writeback,
// compound assignment, direct parameter writes, mutable references stored in
// aggregate fields, Verus-only old/final/current/future state, and
// prophecy/resolvedness helpers. Solver Unknown outcomes are not listed as
// expected evidence.

#![allow(dead_code)]

struct MutRefsPair {
    x: u64,
    y: u64,
}

struct MutRefsRefPair<'a> {
    x: &'a mut u64,
    y: u64,
}

fn mut_refs_id_u64(value: u64) -> u64 {
    value
}

fn mut_refs_read_shared(_value: &u64) {}

pub const MUT_REFS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_basic_no_update",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_basic_direct_update",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_direct_update_wrong_old_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_basic_field_update",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_field_borrow_update_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_reborrow_update_currently_blocked",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_nested_reassign_mut_ref_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_nested_reassign_wrong_target_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_basic_mut_ref_in_pair_write_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_assign_op_add_assign_verified",
        "",
        "verified",
        4,
    ),
    (
        "mut_refs_copy_from_behind_mut_ref_value_read_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_copy_from_behind_mut_ref_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_copy_from_behind_mut_ref_id_value_read_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_auto_coerce_to_shared_borrow_verified",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_auto_coerce_to_shared_borrow_direct_call_verified",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_param_scalar_write_currently_blocked",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_param_scalar_write_via_local_alias_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_assign_op_field_add_assign_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_control_flow_conditional_local_write_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_control_flow_conditional_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_control_flow_tuple_pair_write_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_moves_via_let_tuple_write_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_short_circuit_alias_reassignment_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_assign_in_rhs_alias_reassignment_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_compound_primitive_eval_order_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_has_resolved_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_after_borrow_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_mut_ref_current_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_mut_ref_future_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_final_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_old_state_currently_blocked",
        "",
        "error",
        0,
    ),
];

pub const MUT_REFS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "mut_refs_basic_mut_ref_in_pair_write_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* u_ref . x",
        ],
    ),
    (
        "mut_refs_assign_op_field_add_assign_currently_blocked",
        &[
            "assignment through a mutable-reference projection is unsupported",
            "x_ref . x",
        ],
    ),
    (
        "mut_refs_control_flow_tuple_pair_write_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref . 0",
        ],
    ),
    (
        "mut_refs_moves_via_let_tuple_write_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* refs2 . 0",
        ],
    ),
    (
        "mut_refs_short_circuit_alias_reassignment_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
            "TrustVc only models direct writes through aliases created by `&mut local`",
        ],
    ),
    (
        "mut_refs_assign_in_rhs_alias_reassignment_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* a_ref",
            "TrustVc only models direct writes through aliases created by `&mut local`",
        ],
    ),
    (
        "mut_refs_compound_primitive_eval_order_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `a`",
            "ensure the variable is declared as a function parameter, let-binding, or quantifier-bound variable",
        ],
    ),
    (
        "mut_refs_has_resolved_currently_blocked",
        &["has_resolved", "unknown return type for function"],
    ),
    (
        "mut_refs_after_borrow_currently_blocked",
        &["after_borrow", "unknown return type for function"],
    ),
    (
        "mut_refs_mut_ref_current_currently_blocked",
        &["mut_ref_current", "unknown return type for function"],
    ),
    (
        "mut_refs_mut_ref_future_currently_blocked",
        &["mut_ref_future", "unknown return type for function"],
    ),
    (
        "mut_refs_final_currently_blocked",
        &["Failed to parse assert!() expression", "expected an expression"],
    ),
    (
        "mut_refs_old_state_currently_blocked",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
];

pub fn mut_refs_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    MUT_REFS_RS_EXPECTED_CASES
}

pub fn mut_refs_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MUT_REFS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(p == 20u64)]
#[trust_vc::ensures(true)]
fn mut_refs_basic_no_update(p: u64) {
    let mut u: u64 = p;
    let u_ref: &mut u64 = &mut u;

    trust_vc::assert!(*u_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_direct_update() {
    let mut u: u64 = 20u64;
    let u_ref: &mut u64 = &mut u;

    *u_ref = 30u64;

    trust_vc::assert!(u == 30u64);
    trust_vc::assert!(*u_ref == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_direct_update_wrong_old_value_counterexample() {
    let mut u: u64 = 20u64;
    let u_ref: &mut u64 = &mut u;

    *u_ref = 30u64;

    trust_vc::assert!(u == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_field_update() {
    let mut u = MutRefsPair { x: 20u64, y: 20u64 };
    let u_ref: &mut MutRefsPair = &mut u;

    u_ref.x = 30u64;

    trust_vc::assert!(u.x == 30u64);
    trust_vc::assert!(u.y == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_field_borrow_update_verified() {
    let mut u = MutRefsPair { x: 20u64, y: 20u64 };
    let u_ref: &mut u64 = &mut u.x;

    *u_ref = 30u64;

    trust_vc::assert!(u.x == 30u64);
    trust_vc::assert!(u.y == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_reborrow_update_currently_blocked() {
    let mut u: u64 = 20u64;
    let u_ref: &mut u64 = &mut u;

    *u_ref = 11u64;

    let u_ref2 = &mut *u_ref;
    let first_read = *u_ref2;
    trust_vc::assert!(first_read == 11u64);

    *u_ref2 = 13u64;

    let second_read = *u_ref;
    trust_vc::assert!(second_read == 13u64);

    *u_ref = 17u64;

    trust_vc::assert!(u == 17u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_nested_reassign_mut_ref_verified() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 10u64;

    let mut x_ref: &mut u64 = &mut x;
    *x_ref = 20u64;

    x_ref = &mut y;
    *x_ref = 30u64;

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(y == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_nested_reassign_wrong_target_counterexample() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 10u64;

    let mut x_ref: &mut u64 = &mut x;
    *x_ref = 20u64;

    x_ref = &mut y;
    *x_ref = 30u64;

    trust_vc::assert!(x == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_basic_mut_ref_in_pair_write_currently_blocked() {
    let mut u: u64 = 20u64;
    let u_ref = MutRefsRefPair {
        x: &mut u,
        y: 70u64,
    };

    *u_ref.x = 30u64;

    trust_vc::assert!(u == 30u64);
    trust_vc::assert!(u_ref.y == 70u64);
}

// De-surrogated 2026-07-18 (scalar `&mut` deref-write support + compound
// assignment lowering): `*x_ref += i` now verifies; discriminator-certified
// genuine (unbounded-overflow probe Counterexamples the falsified variant).
#[trust_vc::requires(i < 1000u64)]
#[trust_vc::ensures(true)]
fn mut_refs_assign_op_add_assign_verified(i: u64) {
    let mut x: u64 = 20u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref += i;

    trust_vc::assert!(x == 20u64 + i);
}

#[trust_vc::requires(i < 1000u64)]
#[trust_vc::ensures(true)]
fn mut_refs_assign_op_field_add_assign_currently_blocked(i: u64) {
    let mut x = MutRefsPair { x: 20u64, y: 30u64 };
    let x_ref: &mut MutRefsPair = &mut x;

    x_ref.x += i;

    trust_vc::assert!(x.x == 20u64 + i);
    trust_vc::assert!(x.y == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_copy_from_behind_mut_ref_value_read_verified() {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    let z = *x_ref;

    trust_vc::assert!(z == 20u64);
    trust_vc::assert!(x == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_copy_from_behind_mut_ref_wrong_value_counterexample() {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    let z = *x_ref;

    trust_vc::assert!(z == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_copy_from_behind_mut_ref_id_value_read_verified() {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    let z = mut_refs_id_u64(*x_ref);

    trust_vc::assert!(z == 20u64);
    trust_vc::assert!(x == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_auto_coerce_to_shared_borrow_verified() {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    let x_ref_shared: &u64 = x_ref;
    trust_vc::assert!(*x_ref_shared == 20u64);
    mut_refs_read_shared(x_ref_shared);
}

#[trust_vc::ensures(true)]
fn mut_refs_auto_coerce_to_shared_borrow_direct_call_verified() {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    mut_refs_read_shared(x_ref);
    trust_vc::assert!(x == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_param_scalar_write_currently_blocked(x: &mut u64) {
    *x = 20u64;

    trust_vc::assert!(*x == 20u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_param_scalar_write_via_local_alias_verified(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = 20u64;

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_control_flow_conditional_local_write_verified(b: bool) {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    if b {
        *x_ref = 20u64;
        trust_vc::assert!(x == 20u64);
    } else {
        *x_ref = 30u64;
        trust_vc::assert!(x == 30u64);
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_control_flow_conditional_false_tail_counterexample(b: bool) {
    let mut x: u64 = 0u64;
    let x_ref: &mut u64 = &mut x;

    if b {
        *x_ref = 20u64;
    } else {
        *x_ref = 30u64;
    }

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_control_flow_tuple_pair_write_currently_blocked(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let x_ref = (&mut x, &mut y);

    if b {
        *x_ref.0 = 20u64;
    } else {
        *x_ref.1 = 30u64;
    }

    trust_vc::assert!(x == 20u64 || y == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_moves_via_let_tuple_write_currently_blocked() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let refs = (&mut x, &mut y);
    let refs2 = refs;

    *refs2.0 = 30u64;

    trust_vc::assert!(x == 30u64);
    trust_vc::assert!(y == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_short_circuit_alias_reassignment_currently_blocked(arg1: u64, arg2: u64) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let mut x_ref = &mut x;

    if {
        x_ref = &mut y;
        arg1 == 0u64
    } && arg2 == 0u64
    {}

    *x_ref = 30u64;

    trust_vc::assert!(x == 0u64);
    trust_vc::assert!(y == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_assign_in_rhs_alias_reassignment_currently_blocked() {
    let mut a: u64 = 0u64;
    let mut a_ref = &mut a;
    let mut b: u64 = 1u64;
    let mut c: u64 = 2u64;

    a_ref = {
        a_ref = &mut b;
        *a_ref = 20u64;
        &mut c
    };
    *a_ref = 30u64;

    trust_vc::assert!(a == 0u64);
    trust_vc::assert!(b == 20u64);
    trust_vc::assert!(c == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_compound_primitive_eval_order_currently_blocked() {
    let mut a: u64 = 0u64;
    let a_ref = &mut a;
    let mut x = [0u64, 1u64];

    x[{
        *a_ref = 1u64;
        0usize
    }] += {
        *a_ref = 2u64;
        2u64
    };

    trust_vc::assert!(a == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_has_resolved_currently_blocked() {
    let mut u: u64 = 20u64;
    let u_ref: &mut u64 = &mut u;

    *u_ref = 30u64;

    trust_vc::assert!(has_resolved(u_ref));
}

#[trust_vc::ensures(true)]
fn mut_refs_after_borrow_currently_blocked() {
    let x: u64 = 0u64;

    trust_vc::assert!(after_borrow(x) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_mut_ref_current_currently_blocked(x: &mut u64) {
    trust_vc::assert!(mut_ref_current(x) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_mut_ref_future_currently_blocked(x: &mut u64) {
    trust_vc::assert!(mut_ref_future(x) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_final_currently_blocked(x: &mut u64) {
    trust_vc::assert!(*final(x) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_state_currently_blocked() {
    let mut u: u64 = 20u64;
    let u_ref: &mut u64 = &mut u;

    *u_ref = 30u64;

    trust_vc::assert!(old(u) == 20u64);
}
