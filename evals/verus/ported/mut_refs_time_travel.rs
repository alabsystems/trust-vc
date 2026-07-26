// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_time_travel.rs`.
//
// The upstream file exercises Verus' `new-mut-ref` time-travel checks:
// spec reads of places while they are mutably borrowed, reborrow diagnostics,
// pattern and closure captures, field-sensitive borrows, `after_borrow`,
// `has_resolved`, `old`, quantifiers, and loop contract ordering.
//
// This scout intentionally keeps the manifest row as `unsupported-gap` and
// records only stable source-extraction evidence TrustVc can execute today:
// - direct local mutable-reference writes and current-state reads;
// - direct mutable-reference parameter writes adjacent to `param_old_use_ok`;
// - a snapshot-before-write analogue adjacent to upstream after_borrow cases;
// - field-sensitive borrowed-field writes and different-field snapshots,
//   including auto-dereferenced mutable-reference receiver shapes;
// - a concrete stale-snapshot counterexample; and
// - fail-closed boundaries for explicit dereference receiver projections,
//   Verus-only resolution/snapshot helpers, and old-state mutable-reference
//   snapshots.

#![allow(dead_code)]

struct MutRefsTimeTravelPair {
    left: u64,
    right: u64,
}

pub const MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_time_travel_local_post_write_verified",
        "test_basic_fails post-write executable subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_snapshot_before_write_verified",
        "test_ok_with_after_borrow executable snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_param_current_update_verified",
        "param_old_use_ok executable current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_field_borrow_write_verified",
        "borrow_field_and_use_different_field field-borrow write subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_field_snapshot_before_write_verified",
        "borrow_field_and_use_different_field2 different-field snapshot subset",
        "verified",
        3,
    ),
    (
        "mut_refs_time_travel_deref_different_field_current_verified",
        "borrow_field_and_use_different_field_with_deref current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_deref_different_field_snapshot_verified",
        "borrow_field_and_use_different_field_with_deref2 snapshot subset",
        "verified",
        3,
    ),
    (
        "mut_refs_time_travel_explicit_deref_different_field_current_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref current-state subset",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_explicit_deref_different_field_snapshot_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref2 snapshot subset",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_stale_snapshot_after_write_counterexample",
        "test_ok_with_after_borrow stale snapshot analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_time_travel_after_borrow_currently_blocked",
        "test_ok_with_after_borrow after_borrow boundary",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_has_resolved_currently_blocked",
        "test_ok_with_has_resolved has_resolved boundary",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_old_mut_ref_snapshot_currently_blocked",
        "cant_cheat_prophecy_with_assign_in_old old(x_ref) boundary",
        "error",
        0,
    ),
    // AUDITED FLIP 2026-07-09: slice B: entry-rendered old() over an unconstrained param refutes (probed: value = 1)
    (
        "mut_refs_time_travel_param_old_snapshot_currently_blocked",
        "param_old_use_ok old(x) parameter snapshot boundary",
        "counterexample",
        1,
    ),
];

pub fn mut_refs_time_travel_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_local_post_write_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 20u64;

    trust_vc::assert!(value == 20u64);
    trust_vc::assert!(*value_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_snapshot_before_write_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let snapshot = *value_ref;

    *value_ref = 20u64;

    trust_vc::assert!(snapshot == 0u64);
    trust_vc::assert!(value == 20u64);
}

#[trust_vc::requires(value == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_time_travel_param_current_update_verified(value: &mut u64) {
    let value_ref: &mut u64 = value;

    *value_ref = 20u64;

    trust_vc::assert!(value == 20u64);
    trust_vc::assert!(*value_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_field_borrow_write_verified() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let left_ref: &mut u64 = &mut pair.left;

    trust_vc::assert!(pair.right == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!(pair.left == 20u64);
    trust_vc::assert!(pair.right == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_field_snapshot_before_write_verified() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let left_ref: &mut u64 = &mut pair.left;
    let right_snapshot = pair.right;

    trust_vc::assert!(right_snapshot == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!(pair.left == 20u64);
    trust_vc::assert!(pair.right == right_snapshot);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_deref_different_field_current_verified() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let pair_ref: &mut MutRefsTimeTravelPair = &mut pair;
    let left_ref: &mut u64 = &mut pair_ref.left;

    trust_vc::assert!(pair_ref.right == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!(pair_ref.left == 20u64);
    trust_vc::assert!(pair_ref.right == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_deref_different_field_snapshot_verified() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let pair_ref: &mut MutRefsTimeTravelPair = &mut pair;
    let left_ref: &mut u64 = &mut pair_ref.left;
    let right_snapshot = pair_ref.right;

    trust_vc::assert!(right_snapshot == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!(pair_ref.left == 20u64);
    trust_vc::assert!(pair_ref.right == right_snapshot);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_explicit_deref_different_field_current_currently_blocked() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let pair_ref: &mut MutRefsTimeTravelPair = &mut pair;
    let left_ref: &mut u64 = &mut (*pair_ref).left;

    trust_vc::assert!((*pair_ref).right == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!((*pair_ref).left == 20u64);
    trust_vc::assert!((*pair_ref).right == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_explicit_deref_different_field_snapshot_currently_blocked() {
    let mut pair = MutRefsTimeTravelPair {
        left: 0u64,
        right: 1u64,
    };
    let pair_ref: &mut MutRefsTimeTravelPair = &mut pair;
    let left_ref: &mut u64 = &mut (*pair_ref).left;
    let right_snapshot = (*pair_ref).right;

    trust_vc::assert!(right_snapshot == 1u64);

    *left_ref = 20u64;

    trust_vc::assert!((*pair_ref).left == 20u64);
    trust_vc::assert!((*pair_ref).right == right_snapshot);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_stale_snapshot_after_write_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let snapshot = *value_ref;

    *value_ref = 20u64;

    trust_vc::assert!(snapshot == value);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_after_borrow_currently_blocked(value: u64) {
    trust_vc::assert!(after_borrow(value) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_has_resolved_currently_blocked(value: &mut u64) {
    trust_vc::assert!(has_resolved(value));
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_old_mut_ref_snapshot_currently_blocked() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 20u64;

    trust_vc::assert!(*old(value_ref) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_time_travel_param_old_snapshot_currently_blocked(value: &mut u64) {
    let value_ref: &mut u64 = value;

    *value_ref = 20u64;

    trust_vc::assert!(*old(value) == 0u64);
}
