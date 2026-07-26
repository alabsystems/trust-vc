// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_modes.rs`.
//
// The upstream file is mostly Verus mode-system behavior for mutable
// references: ghost/proof/tracked places, `has_resolved`, `final`/`old` mutable
// reference post-state, `tracked_swap`, `tracked_take`, overloaded
// Ghost/Tracked deref, and `mut_ref_tracked`.
//
// This Rust-valid scout intentionally covers only the stable executable slice
// TrustVc can express today:
// - direct exec-mode local/parameter `&mut` borrowing, field writes, field
//   borrows, and two-local swapping;
// - Ghost<T> and Tracked<T> wrapper read/copy shapes adjacent to upstream
//   ghost/tracked place read cases;
// - concrete counterexamples for stale snapshots and wrong post-state claims;
// - fail-closed boundaries for Verus-only `has_resolved`, old-state
//   mutable-reference reasoning, Ghost tuple projection/construction, Tracked
//   get/borrow helpers, `tracked_swap`, `tracked_take`, and `mut_ref_tracked`.
//
// The manifest entry remains `unsupported-gap`.

#![allow(dead_code)]

use trust_vc_types::{Ghost, Tracked};

pub type MutRefsModesExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type MutRefsModesFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

struct MutRefsModesPair {
    x: u64,
    y: u64,
}

pub const MUT_REFS_MODES_RS_EXPECTED_CASES: &[MutRefsModesExpectedCase] = &[
    (
        "mut_refs_modes_exec_local_mut_borrow_verified",
        "mut_borrow_of_exec_local_in_tracked_local_decl executable analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_struct_field_mut_ref_write_verified",
        "modify_exec_place_in_proof_code executable struct-field analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_field_borrow_write_verified",
        "mut_ref_tracked_place_in_proof_code executable field-borrow analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_param_alias_write_verified",
        "tracked_swap_requires_non_exec_place2 executable parameter-alias analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_verified",
        "tracked_swap_requires_non_exec_place executable two-local swap analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_ghost_wrapper_snapshot_read_verified",
        "ghost_places_dont_count_as_moves executable Ghost<T> snapshot analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_copy_read_verified",
        "ghost_overloaded_deref_1 Ghost<T> copy/view analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_copy_verified",
        "tracked_overloaded_deref_1 Tracked<T> copy wrapper analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_stale_exec_snapshot_counterexample",
        "ghost_places_dont_resolve stale snapshot analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_wrong_post_counterexample",
        "tracked_swap_requires_non_exec_place wrong post-state analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_false_tail_counterexample",
        "ghost_overloaded_deref_1 Ghost<T> false-tail analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_false_tail_counterexample",
        "tracked_overloaded_deref_1 Tracked<T> false-tail analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_has_resolved_currently_blocked",
        "resolve_tracked_param_but_not_ghost_param",
        "error",
        0,
    ),
    (
        "mut_refs_modes_old_state_after_mut_ref_write_currently_blocked",
        "wrapped_params",
        "error",
        0,
    ),
    (
        "mut_refs_modes_ghost_tuple_projection_verified",
        "ghost_auto_deref_1 Ghost<T> tuple projection boundary",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_ghost_constructor_currently_blocked",
        "modify_ghost_wrapped_type_in_proof_code Ghost constructor boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_get_currently_blocked",
        "tracked_overloaded_deref_1 Tracked<T> get boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_borrow_currently_blocked",
        "tracked_auto_deref_1 Tracked<T> borrow boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_swap_currently_blocked",
        "tracked_swap_requires_non_exec_place",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_take_currently_blocked",
        "tracked_take_requires_non_exec_place",
        "error",
        0,
    ),
    (
        "mut_refs_modes_mut_ref_tracked_currently_blocked",
        "mut_ref_tracked3",
        "error",
        0,
    ),
];

pub fn mut_refs_modes_rs_expected_cases() -> &'static [MutRefsModesExpectedCase] {
    MUT_REFS_MODES_RS_EXPECTED_CASES
}

pub const MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS: &[MutRefsModesFailClosedErrorPatterns] = &[
    (
        "mut_refs_modes_has_resolved_currently_blocked",
        &["has_resolved"],
    ),
    (
        "mut_refs_modes_old_state_after_mut_ref_write_currently_blocked",
        &["Unsupported old-state expression `old(...)`", "old"],
    ),
    (
        "mut_refs_modes_ghost_constructor_currently_blocked",
        &["Ghost::new"],
    ),
    ("mut_refs_modes_tracked_get_currently_blocked", &["get"]),
    (
        "mut_refs_modes_tracked_borrow_currently_blocked",
        &["borrow"],
    ),
    (
        "mut_refs_modes_tracked_swap_currently_blocked",
        &["tracked_swap"],
    ),
    (
        "mut_refs_modes_tracked_take_currently_blocked",
        &["tracked_take"],
    ),
    (
        "mut_refs_modes_mut_ref_tracked_currently_blocked",
        &["&mut not supported"],
    ),
];

pub fn mut_refs_modes_rs_fail_closed_error_patterns(
) -> &'static [MutRefsModesFailClosedErrorPatterns] {
    MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_local_mut_borrow_verified() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_struct_field_mut_ref_write_verified() {
    let mut x = MutRefsModesPair { x: 4u64, y: 6u64 };
    let x_ref: &mut MutRefsModesPair = &mut x;

    x_ref.x = 20u64;

    trust_vc::assert!(x.x == 20u64);
    trust_vc::assert!(x.y == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_field_borrow_write_verified() {
    let mut x = MutRefsModesPair { x: 4u64, y: 6u64 };
    let x_ref: &mut u64 = &mut x.x;

    *x_ref = 20u64;

    trust_vc::assert!(x.x == 20u64);
    trust_vc::assert!(x.y == 6u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_param_alias_write_verified(x: &mut u64) {
    let x_ref: &mut u64 = x;

    *x_ref = 20u64;

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_two_local_swap_verified() {
    let mut a = 0u64;
    let mut b = 1u64;
    let a_ref: &mut u64 = &mut a;
    let b_ref: &mut u64 = &mut b;

    let old_a = *a_ref;
    *a_ref = *b_ref;
    *b_ref = old_a;

    trust_vc::assert!(a == 1u64);
    trust_vc::assert!(b == 0u64);
}

#[trust_vc::requires(g.view() == 3u64)]
#[trust_vc::ensures(true)]
fn mut_refs_modes_ghost_wrapper_snapshot_read_verified(g: Ghost<u64>) {
    let snapshot = g;

    trust_vc::assert!(g.view() == 3u64);
    trust_vc::assert!(snapshot.view() == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_ghost_wrapper_copy_read_verified(g: Ghost<u64>) {
    let first = g;
    let second = g;

    trust_vc::assert!(first.view() == second.view());
}

#[trust_vc::proof]
fn mut_refs_modes_tracked_wrapper_copy_verified(t: Tracked<u64>) {
    let first = t;
    let second = t;
    let _ = (first, second);

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_stale_exec_snapshot_counterexample() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;
    let snapshot = *x_ref;

    *x_ref = 20u64;

    trust_vc::assert!(snapshot == x);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_exec_two_local_swap_wrong_post_counterexample() {
    let mut a = 0u64;
    let mut b = 1u64;
    let a_ref: &mut u64 = &mut a;
    let b_ref: &mut u64 = &mut b;

    let old_a = *a_ref;
    *a_ref = *b_ref;
    *b_ref = old_a;

    trust_vc::assert!(a == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_ghost_wrapper_false_tail_counterexample(g: Ghost<u64>) {
    trust_vc::assert!(g.view() == g.view());
    trust_vc::assert!(false);
}

#[trust_vc::proof]
fn mut_refs_modes_tracked_wrapper_false_tail_counterexample(t: Tracked<u64>) {
    let _ = t;
    trust_vc::assert!(false);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding / tuple-projection rework):
// `g.view().0` on a Ghost<(u64, u64)> now projects and verifies;
// discriminator-certified genuine (`.0 == .1` distinctness Counterexamples).
#[trust_vc::ensures(true)]
fn mut_refs_modes_ghost_tuple_projection_verified(g: Ghost<(u64, u64)>) {
    trust_vc::assert!(g.view().0 == g.view().0);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_ghost_constructor_currently_blocked() {
    let g = Ghost::new(3u64);
    trust_vc::assert!(g.view() == 3u64);
}

#[trust_vc::proof]
fn mut_refs_modes_tracked_get_currently_blocked(t: Tracked<u64>) {
    let value = t.get();
    trust_vc::assert!(value == value);
}

#[trust_vc::proof]
fn mut_refs_modes_tracked_borrow_currently_blocked(t: Tracked<u64>) {
    let value = t.borrow();
    trust_vc::assert!(*value == *value);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_has_resolved_currently_blocked(x: &mut u64) {
    trust_vc::assert!(has_resolved(x));
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_old_state_after_mut_ref_write_currently_blocked() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    trust_vc::assert!(old(x) == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_tracked_swap_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let a_ref: &mut u64 = &mut a;
    let b_ref: &mut u64 = &mut b;

    trust_vc::assert!(tracked_swap(a_ref, b_ref));
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_tracked_take_currently_blocked(x: &mut Option<u64>) {
    trust_vc::assert!(x.tracked_take().is_some());
}

#[trust_vc::ensures(true)]
fn mut_refs_modes_mut_ref_tracked_currently_blocked() {
    let mut u = 0u64;
    trust_vc::assert!(mut_ref_tracked(&mut u));
}
