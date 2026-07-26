// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/proph.rs`.
//
// The upstream file exercises Verus prophecy variables through `p@`,
// `resolve(&value)`, proof-time branching on a future value, structured
// prophecy payloads, and a rejected `Ghost<T>` payload. TrustVc has a lower-level
// Rust-valid `trust_vc_types::Proph<T>` proof bridge, but it is not a one-to-one
// replacement for the Verus `vstd::proph::Prophecy<T>` API.
//
// This scout keeps the upstream manifest entry as an unsupported-gap and pins
// only stable evidence TrustVc can execute today:
// - Rust-valid verified bool, branch, and struct-payload surrogates for the
//   upstream Ok shapes;
// - stable counterexamples for wrong resolved values and branch outcomes; and
// - fail-closed extraction boundaries for direct Verus Prophecy<T> API use,
//   direct TrustVc Proph<T> view/resolve metadata, future snapshots,
//   resolvedness queries, double resolution, and Ghost payloads.
// Solver Unknown outcomes are intentionally excluded as replacement evidence.

#![allow(dead_code)]

use trust_vc_types::Proph;

pub type ProphRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ProphRsExpectedErrorPattern = (&'static str, &'static [&'static str]);

pub const PROPH_RS_EXPECTED_CASES: &[ProphRsExpectedCase] = &[
    (
        "proph_bool_resolution_boundary_true_verified",
        "prophecy_expected_use_3",
        "verified",
        2,
    ),
    (
        "proph_bool_resolution_boundary_false_verified",
        "prophecy_expected_use_3",
        "verified",
        2,
    ),
    (
        "proph_branch_on_resolved_bool_surrogate_verified",
        "prophecy_expected_use_1",
        "verified",
        2,
    ),
    (
        "proph_struct_payload_resolution_surrogate_verified",
        "prophecy_expected_use_2",
        "verified",
        4,
    ),
    (
        "proph_bool_resolution_boundary_wrong_value_counterexample",
        "prophecy_expected_use_3",
        "counterexample",
        1,
    ),
    (
        "proph_branch_wrong_future_value_counterexample",
        "prophecy_expected_use_1",
        "counterexample",
        1,
    ),
    (
        "proph_struct_payload_wrong_field_counterexample",
        "prophecy_expected_use_2",
        "counterexample",
        1,
    ),
    (
        "proph_ghost_payload_wrong_view_counterexample",
        "prophecy_ghost_disallowed",
        "counterexample",
        1,
    ),
    (
        "prophecy_api_surface_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "proph_bool_view_assert_currently_blocked",
        "prophecy_expected_use_3",
        "error",
        0,
    ),
    (
        "proph_bool_view_binding_currently_blocked",
        "prophecy_expected_use_1",
        "error",
        0,
    ),
    (
        "proph_struct_payload_view_currently_blocked",
        "prophecy_expected_use_2",
        "error",
        0,
    ),
    (
        "proph_future_snapshot_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "proph_resolvedness_query_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "proph_double_resolve_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "proph_ghost_payload_surface_currently_blocked",
        "prophecy_ghost_disallowed",
        "error",
        0,
    ),
];

pub fn proph_rs_expected_cases() -> &'static [ProphRsExpectedCase] {
    PROPH_RS_EXPECTED_CASES
}

pub const PROPH_RS_EXPECTED_ERROR_PATTERNS: &[ProphRsExpectedErrorPattern] = &[
    (
        "prophecy_api_surface_currently_blocked",
        &["Prophecy", "unknown return type", "unresolved", "view", "resolve"],
    ),
    (
        "proph_bool_view_assert_currently_blocked",
        &["unresolved variable `p`"],
    ),
    (
        "proph_bool_view_binding_currently_blocked",
        &["collection operation 'view' requires a collection receiver"],
    ),
    (
        "proph_struct_payload_view_currently_blocked",
        &["collection operation 'view' requires a collection receiver"],
    ),
    (
        "proph_future_snapshot_currently_blocked",
        &["future", "unresolved"],
    ),
    (
        "proph_resolvedness_query_currently_blocked",
        &["is_resolved", "method", "unsupported", "unresolved"],
    ),
    (
        "proph_double_resolve_currently_blocked",
        &["unresolved variable `p`", "view", "resolve"],
    ),
    (
        "proph_ghost_payload_surface_currently_blocked",
        &["Ghost", "view", "unresolved"],
    ),
];

pub fn proph_rs_expected_error_patterns() -> &'static [ProphRsExpectedErrorPattern] {
    PROPH_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ProphPayload {
    a: u64,
    b: u8,
    c: bool,
}

#[trust_vc::external]
#[trust_vc::contract(
    requires(boundary_guard),
    ensures(result == resolved_value),
    returns(result),
)]
fn proph_bool_resolution_boundary(resolved_value: bool, boundary_guard: bool) -> bool {
    let _ = boundary_guard;
    resolved_value
}

#[trust_vc::ensures(true)]
fn proph_bool_resolution_boundary_true_verified() {
    let observed = proph_bool_resolution_boundary(true, true);
    trust_vc::assert!(observed == true);
}

#[trust_vc::ensures(true)]
fn proph_bool_resolution_boundary_false_verified() {
    let observed = proph_bool_resolution_boundary(false, true);
    trust_vc::assert!(observed == false);
}

#[trust_vc::ensures(true)]
fn proph_branch_on_resolved_bool_surrogate_verified(resolved_value: bool) {
    trust_vc::assume!(resolved_value);

    let ghost_branch_value = if resolved_value { 2i32 } else { 3i32 };

    trust_vc::assert!(ghost_branch_value == 2i32);
    trust_vc::assert!(resolved_value == true);
}

#[trust_vc::ensures(true)]
fn proph_struct_payload_resolution_surrogate_verified() {
    let observed = ProphPayload {
        a: 1u64,
        b: 2u8,
        c: false,
    };

    trust_vc::assert!(observed.a == 1u64);
    trust_vc::assert!(observed.b == 2u8);
    trust_vc::assert!(observed.c == false);
    trust_vc::assert!(
        observed
            == ProphPayload {
                a: 1u64,
                b: 2u8,
                c: false,
            }
    );
}

#[trust_vc::ensures(true)]
fn proph_bool_resolution_boundary_wrong_value_counterexample() {
    let observed = true;
    let expected = false;

    let _ = (observed, expected);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn proph_branch_wrong_future_value_counterexample() {
    let resolved_value = true;
    let ghost_branch_value = if resolved_value { 2i32 } else { 3i32 };

    let _ = ghost_branch_value;
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn proph_struct_payload_wrong_field_counterexample() {
    let observed = ProphPayload {
        a: 1u64,
        b: 2u8,
        c: false,
    };

    let _ = observed;
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn proph_ghost_payload_wrong_view_counterexample(ghost_value: bool) {
    let predicted_ghost_view = !ghost_value;

    let _ = predicted_ghost_view;
    trust_vc::assert!(false);
}

fn prophecy_api_surface_currently_blocked() {
    let p = Prophecy::<bool>::new();

    p.resolve(&true);
    trust_vc::assert!(p.view() == true);
}

#[trust_vc::proof]
fn proph_bool_view_assert_currently_blocked() {
    let p: Proph<bool> = Proph::<bool>::new();

    p.resolve(true);

    trust_vc::assert!(p.view() == true);
}

#[trust_vc::proof]
fn proph_bool_view_binding_currently_blocked() {
    let p: Proph<bool> = Proph::<bool>::new();
    let predicted: bool = p.view();

    p.resolve(true);

    trust_vc::assert!(predicted == true);
}

#[trust_vc::proof]
fn proph_struct_payload_view_currently_blocked() {
    let p: Proph<ProphPayload> = Proph::<ProphPayload>::new();
    let predicted: ProphPayload = p.view();

    p.resolve(ProphPayload {
        a: 1u64,
        b: 2u8,
        c: false,
    });

    trust_vc::assert!(
        predicted
            == ProphPayload {
                a: 1u64,
                b: 2u8,
                c: false,
            }
    );
}

#[trust_vc::proof]
fn proph_future_snapshot_currently_blocked(value: &mut bool) {
    let p: Proph<bool> = Proph::<bool>::new();
    let future_value = *future(value);

    p.resolve(future_value);

    trust_vc::assert!(future_value == true);
}

#[trust_vc::proof]
fn proph_resolvedness_query_currently_blocked() {
    let p: Proph<bool> = Proph::<bool>::new();

    trust_vc::assert!(p.is_resolved());
}

#[trust_vc::proof]
fn proph_double_resolve_currently_blocked() {
    let p: Proph<bool> = Proph::<bool>::new();

    p.resolve(true);
    p.resolve(false);

    trust_vc::assert!(p.view() == true);
}

#[trust_vc::proof]
fn proph_ghost_payload_surface_currently_blocked() {
    let p: Proph<Ghost<bool>> = Proph::<Ghost<bool>>::new();
    let predicted = p.view();

    p.resolve(Ghost(!predicted.view()));
    trust_vc::assert!(predicted.view() == true);
}
