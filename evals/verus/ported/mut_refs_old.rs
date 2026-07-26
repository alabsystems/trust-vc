// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_old.rs`.
//
// The upstream file exercises Verus' `new-mut-ref` old/final state model:
// mutable-reference parameters, tuple field projections, closure-local
// contracts, nested mutable references, `opens_invariants`, decreases,
// returns/unwind specs, and exact diagnostics for `old`/`final` misuse.
// TrustVc does not currently expose that Verus snapshot model through source
// extraction.
//
// This scout keeps the manifest entry `unsupported-gap` and records only
// Rust-valid behavior TrustVc can execute today:
// - direct scalar mutable-reference parameter writes, adjacent to upstream
//   `old_in_body`;
// - explicit snapshot-before-write locals that act only as Rust-valid
//   surrogates for upstream `old(...)` facts;
// - direct local mutable-reference writes that prove the current value after an
//   update, adjacent to upstream `old_in_body`;
// - a concrete field update through a direct mutable local alias, adjacent to
//   upstream tuple-field current-state checks;
// - a current-state returns-contract subset adjacent to upstream
//   `mutable_param_used_in_returns`;
// - stale-current-value and stale-snapshot counterexamples;
// - an explicit field-fail counterexample adjacent to upstream
//   `old_in_body::test_field_fail`; and
// - explicit fail-closed boundaries for `old(...)`, `final(...)`, nested
//   mutable-reference history helpers, spec/closure old-state use, and tuple
//   mutable-reference projections.

#![allow(dead_code)]

struct MutRefsOldPair {
    left: u64,
    right: u64,
}

pub const MUT_REFS_OLD_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_old_param_current_update_verified",
        "old_in_body::test scalar &mut parameter current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_param_snapshot_before_update_verified",
        "old_in_body::test scalar &mut parameter manual old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_local_current_update_verified",
        "old_in_body::test current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_local_snapshot_before_update_verified",
        "old_in_body::test manual old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_field_current_update_verified",
        "old_in_body::test_field direct-field current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_field_snapshot_before_update_verified",
        "old_in_body::test_field manual tuple-field old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_returns_current_contract_verified",
        "mutable_param_used_in_returns current-state return-contract subset",
        "verified",
        1,
    ),
    (
        "mut_refs_old_stale_current_value_counterexample",
        "old_in_body::test_fail stale current-value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_snapshot_wrong_after_update_counterexample",
        "old_in_body::test_fail stale manual old-snapshot assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_field_assert_false_counterexample",
        "old_in_body::test_field_fail explicit false assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_returns_old_contract_currently_blocked",
        "mutable_param_used_in_returns old mutable-reference return contract",
        "error",
        0,
    ),
    (
        "mut_refs_old_local_old_snapshot_currently_blocked",
        "old_in_body::test old(x) snapshot boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_local_final_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok final(value) snapshot boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_final_mut_ref_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok *final(x) mutable-reference boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_tuple_field_old_snapshot_currently_blocked",
        "old_in_body::test_field tuple projection old(x.0) boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_nested_current_history_currently_blocked",
        "nested_mut_refs mut_ref_current history boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_nested_future_history_currently_blocked",
        "nested_mut_refs mut_ref_future history boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_spec_fn_old_snapshot_currently_blocked",
        "old_in_spec_fn old(x) spec-function boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_closure_old_snapshot_currently_blocked",
        "old_in_closure_body old(x) closure boundary",
        "error",
        0,
    ),
];

pub fn mut_refs_old_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_OLD_RS_EXPECTED_CASES
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_old_param_current_update_verified(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = 5u64;

    trust_vc::assert!(x == 5u64);
    trust_vc::assert!(*x_ref == 5u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_old_param_snapshot_before_update_verified(x: &mut u64) {
    let x_ref: &mut u64 = x;
    let before = *x_ref;

    *x_ref = 5u64;

    trust_vc::assert!(before == 0u64);
    trust_vc::assert!(x == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_local_current_update_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 5u64;

    trust_vc::assert!(value == 5u64);
    trust_vc::assert!(*value_ref == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_local_snapshot_before_update_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let before = *value_ref;

    *value_ref = 5u64;

    trust_vc::assert!(before == 0u64);
    trust_vc::assert!(value == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_field_current_update_verified() {
    let mut pair = MutRefsOldPair {
        left: 0u64,
        right: 10u64,
    };
    let pair_ref: &mut MutRefsOldPair = &mut pair;

    pair_ref.left = 5u64;

    trust_vc::assert!(pair.left == 5u64);
    trust_vc::assert!(pair.right == 10u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_field_snapshot_before_update_verified() {
    let mut pair = MutRefsOldPair {
        left: 0u64,
        right: 10u64,
    };
    let pair_ref: &mut MutRefsOldPair = &mut pair;
    let left_before = pair_ref.left;

    pair_ref.left = 5u64;

    trust_vc::assert!(left_before == 0u64);
    trust_vc::assert!(pair.left == 5u64);
    trust_vc::assert!(pair.right == 10u64);
}

#[trust_vc::contract(
    requires(x == 0u64),
    ensures(ret == 0u64),
    returns(ret),
)]
fn mut_refs_old_returns_current_contract_verified(x: &mut u64) -> u64 {
    let x_ref: &mut u64 = x;
    *x_ref = 1u64;
    0u64
}

#[trust_vc::ensures(true)]
fn mut_refs_old_stale_current_value_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 5u64;

    trust_vc::assert!(value == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_snapshot_wrong_after_update_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let before = *value_ref;

    *value_ref = 5u64;

    trust_vc::assert!(before == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_field_assert_false_counterexample() {
    let mut pair = MutRefsOldPair {
        left: 0u64,
        right: 10u64,
    };
    let pair_ref: &mut MutRefsOldPair = &mut pair;

    pair_ref.left = 5u64;

    trust_vc::assert!(pair.left == 5u64);
    trust_vc::assert!(false);
}

#[trust_vc::contract(
    requires(x < 100u64),
    ensures(ret == old!(*x)),
    returns(ret),
)]
fn mut_refs_old_returns_old_contract_currently_blocked(x: &mut u64) -> u64 {
    let x_ref: &mut u64 = x;
    let before = *x_ref;
    *x_ref = before + 1u64;
    before
}

#[trust_vc::ensures(true)]
fn mut_refs_old_local_old_snapshot_currently_blocked() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 5u64;

    trust_vc::assert!(old(value) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_local_final_snapshot_currently_blocked() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 5u64;

    trust_vc::assert!(final(value) == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_final_mut_ref_snapshot_currently_blocked() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 5u64;

    trust_vc::assert!(*final(value_ref) == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_tuple_field_old_snapshot_currently_blocked() {
    let mut left = 0u64;
    let mut right = 10u64;
    let pair = (&mut left, &mut right);

    *pair.0 = 5u64;

    trust_vc::assert!(*old(pair.0) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_nested_current_history_currently_blocked(x: &mut &mut u64) {
    trust_vc::assert!(mut_ref_current(mut_ref_current(x)) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_old_nested_future_history_currently_blocked(x: &mut &mut u64) {
    trust_vc::assert!(mut_ref_future(mut_ref_future(x)) == 19u64);
}

#[trust_vc::spec]
fn mut_refs_old_spec_fn_old_snapshot_currently_blocked(x: &mut u64) -> u64 {
    *old(x)
}

#[trust_vc::ensures(true)]
fn mut_refs_old_closure_old_snapshot_currently_blocked() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let check_old = || {
        trust_vc::assert!(*old(value_ref) == 0u64);
    };

    *value_ref = 5u64;

    check_old();
}
