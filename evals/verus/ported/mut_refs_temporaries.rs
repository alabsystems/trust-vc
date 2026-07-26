// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_temporaries.rs`.
//
// The upstream file is a large `new-mut-ref` suite for temporary places:
// assignment and assignment-op through tuple temporaries, helper-returned
// mutable references, block-expression side effects, let/match pattern
// destructuring, constructor update syntax, shared borrows, unused temporaries,
// nested mutable references, ghost/tracked temporaries, overflow diagnostics,
// `has_resolved`, `mut_ref_current`, and `mut_ref_future`.
//
// This scout keeps the manifest row as `unsupported-gap` and records only
// stable Rust-valid TrustVc evidence available today:
// - value tuple temporary assignment and assignment-op do not update their
//   source locals;
// - wrong assertions about those source locals are rejected;
// - direct temporary mutable-reference writes update their source local, while
//   stale post-write assertions are rejected;
// - shared borrows of value tuple temporaries preserve the source locals; and
// - value tuple field reads, shared borrows of mutable-reference temporaries,
//   assignment-op through mutable-reference temporaries, helper-returned mutable
//   references, block-expression side effects, tuple-projected
//   mutable-reference temporary writes, and Verus resolution predicates stay
//   fail-closed.

#![allow(dead_code)]

pub const MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_temporaries_tuple_value_assignment_verified",
        "temporary_place_in_assign::test3 value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_verified",
        "temporary_place_in_assign_op::test3 value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_tuple_value_wrong_source_counterexample",
        "temporary_place_in_assign::test3 wrong source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_wrong_source_counterexample",
        "temporary_place_in_assign_op::test3 wrong source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_tuple_value_field_read_currently_blocked",
        "temporary_place_in_let_stmt value tuple field-read boundary",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assignment_verified",
        "temporary_place_in_assign::test2 direct temporary mutable-reference write",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_stale_source_counterexample",
        "temporary_place_in_assign::test2 stale source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assign_op_currently_blocked",
        "temporary_place_in_assign_op::test2 direct temporary mutable-reference assignment-op",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_helper_returned_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test1 helper-returned temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_tuple_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test4 tuple-projected temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_shared_direct_mut_borrow_currently_blocked",
        "temporary_place_in_shared_borrow::test2 shared borrow of direct temporary mutable reference",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_shared_tuple_value_borrow_sources_verified",
        "temporary_place_in_shared_borrow::test3 shared borrow of value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_block_value_side_effect_currently_blocked",
        "temporary_place_unused::test5 block temporary side-effect boundary",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_block_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test7 block temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_has_resolved_boundary_currently_blocked",
        "temporary_place_in_let_stmt::test2 has_resolved resolution predicate",
        "error",
        0,
    ),
];

pub fn mut_refs_temporaries_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES
}

fn mut_refs_temporaries_mut_ref_pairs<'a, 'b>(
    a: &'a mut u64,
    b: &'b mut u64,
) -> (&'a mut u64, &'b mut u64) {
    (a, b)
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_value_assignment_verified() {
    let mut a: u64 = 0u64;
    let mut b: u64 = 0u64;

    (a, b).0 = 5u64;

    trust_vc::assert!(a == 0u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_value_assign_op_verified() {
    let mut a: u64 = 1u64;
    let mut b: u64 = 1u64;

    (a, b).0 += 5u64;

    trust_vc::assert!(a == 1u64);
    trust_vc::assert!(b == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_value_field_read_currently_blocked() {
    let a: u64 = 2u64;
    let b: u64 = 3u64;
    let x = (a, b).0;

    trust_vc::assert!(x == 2u64);
    trust_vc::assert!(a == 2u64);
    trust_vc::assert!(b == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_value_wrong_source_counterexample() {
    let mut a: u64 = 0u64;
    let mut b: u64 = 0u64;

    (a, b).0 = 5u64;

    trust_vc::assert!(a == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_value_assign_op_wrong_source_counterexample() {
    let mut a: u64 = 1u64;
    let mut b: u64 = 1u64;

    (a, b).0 += 5u64;

    trust_vc::assert!(a == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_direct_mut_borrow_assignment_verified() {
    let mut a: u64 = 0u64;
    let b: u64 = 0u64;

    *(&mut a) = 5u64;

    trust_vc::assert!(a == 5u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_direct_mut_borrow_stale_source_counterexample() {
    let mut a: u64 = 0u64;

    *(&mut a) = 5u64;

    trust_vc::assert!(a == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_direct_mut_borrow_assign_op_currently_blocked() {
    let mut a: u64 = 1u64;
    let b: u64 = 1u64;

    *(&mut a) += 5u64;

    trust_vc::assert!(a == 6u64);
    trust_vc::assert!(b == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_helper_returned_mut_borrow_assignment_currently_blocked() {
    let mut a: u64 = 0u64;
    let mut b: u64 = 0u64;

    *mut_refs_temporaries_mut_ref_pairs(&mut a, &mut b).0 = 5u64;

    trust_vc::assert!(a == 5u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_tuple_mut_borrow_assignment_currently_blocked() {
    let mut a: u64 = 0u64;
    let mut b: u64 = 0u64;

    *(&mut a, &mut b).0 = 5u64;

    trust_vc::assert!(a == 5u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_shared_direct_mut_borrow_currently_blocked() {
    let mut a: u64 = 0u64;
    let b: u64 = 0u64;

    let _shr = &(&mut a);

    trust_vc::assert!(a == 0u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_shared_tuple_value_borrow_sources_verified() {
    let mut a: u64 = 0u64;
    let mut b: u64 = 0u64;

    let _shr = &(a, b).0;

    trust_vc::assert!(a == 0u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_block_value_side_effect_currently_blocked() {
    let a: u64 = 0u64;
    let b: u64 = 0u64;
    let mut y: u64 = 0u64;

    ({
        y = y + 1u64;
        (a, b)
    })
    .0;

    trust_vc::assert!(y == 1u64);
    trust_vc::assert!(a == 0u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_block_mut_borrow_assignment_currently_blocked() {
    let mut a: u64 = 0u64;
    let b: u64 = 0u64;
    let mut y: u64 = 0u64;

    *({
        y = y + 1u64;
        &mut a
    }) = 5u64;

    trust_vc::assert!(y == 1u64);
    trust_vc::assert!(a == 5u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_temporaries_has_resolved_boundary_currently_blocked(a: u64, b: u64) {
    let x = (a, b).0;

    trust_vc::assert!(has_resolved(x));
}
