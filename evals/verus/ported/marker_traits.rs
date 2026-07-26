// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/marker_traits.rs`.
//
// The upstream file macro-generates Rust/Verus tests for Send, Sync, Copy, and
// variance behavior on vstd ghost/tracked/invariant wrapper types. TrustVc does
// not currently expose those vstd marker-wrapper types or Rust compiler
// diagnostics as one-to-one executable evidence.
//
// This scout slice pins the Rust-valid behavior TrustVc can express today:
// - Generic marker bounds are preserved in extracted function contexts.
// - Simple identities under Copy, Send, Sync, Send + Sync, and
//   Copy + Send + Sync marker bounds verify.
// - Concrete Rust-valid Copy/Send/Sync witnesses can call through generic
//   marker-bound helpers.
// - False assertions under simple and combined marker bounds are rejected.
// - Unsupported upstream-shaped vstd marker wrapper types fail closed instead
//   of being encoded as unconstrained values.
// - A Copy-bound const-generic array parameter remains a stable extraction
//   error while const-generic type shapes are unsupported.
// - dyn Send marker-trait objects and vstd variance/lifetime wrapper shapes
//   remain fail-closed unsupported boundaries.
// - Exact Rust/Verus marker diagnostic text remains a fail-closed diagnostic
//   metadata boundary rather than accepted verification behavior.

pub const MARKER_TRAITS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "copy_bound_identity_verified",
        "check_not_copy",
        "verified",
        1,
    ),
    (
        "send_sync_where_bound_identity_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    ("send_bound_identity_verified", "check_send", "verified", 1),
    ("sync_bound_identity_verified", "check_sync", "verified", 1),
    (
        "copy_send_sync_bound_identity_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    (
        "concrete_copy_witness_caller_verified",
        "check_not_copy",
        "verified",
        1,
    ),
    (
        "concrete_send_witness_caller_verified",
        "check_send",
        "verified",
        1,
    ),
    (
        "concrete_sync_witness_caller_verified",
        "check_sync",
        "verified",
        1,
    ),
    (
        "concrete_send_sync_witness_caller_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    (
        "shared_reference_lifetime_identity_verified",
        "",
        "verified",
        1,
    ),
    (
        "copy_bound_false_assert_counterexample",
        "check_not_copy",
        "counterexample",
        1,
    ),
    (
        "send_bound_false_assert_counterexample",
        "check_send",
        "counterexample",
        1,
    ),
    (
        "sync_bound_false_assert_counterexample",
        "check_sync",
        "counterexample",
        1,
    ),
    (
        "send_sync_bound_false_assert_counterexample",
        "check_send_sync",
        "counterexample",
        1,
    ),
    (
        "copy_send_sync_bound_false_assert_counterexample",
        "check_send_sync",
        "counterexample",
        1,
    ),
    (
        "copy_bound_const_generic_array_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "rust_moved_value_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "rust_send_sync_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "verus_variance_lifetime_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
];

pub fn marker_traits_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MARKER_TRAITS_RS_EXPECTED_CASES
}

pub const MARKER_TRAITS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "copy_bound_const_generic_array_currently_errors",
        &["unsupported const-generic array length"],
    ),
    (
        "rust_moved_value_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
    (
        "rust_send_sync_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
    (
        "verus_variance_lifetime_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
];

pub fn marker_traits_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MARKER_TRAITS_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct CopyWitness {
    raw: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SendSyncWitness {
    raw: u64,
}

#[trust_vc::ensures(result == value)]
fn copy_bound_identity_verified<T: Copy>(value: T) -> T {
    value
}

#[trust_vc::ensures(result == value)]
fn send_sync_where_bound_identity_verified<T>(value: T) -> T
where
    T: Send + Sync,
{
    value
}

#[trust_vc::ensures(result == value)]
fn send_bound_identity_verified<T: Send>(value: T) -> T {
    value
}

#[trust_vc::ensures(result == value)]
fn sync_bound_identity_verified<T: Sync>(value: T) -> T {
    value
}

#[trust_vc::ensures(result == value)]
fn copy_send_sync_bound_identity_verified<T: Copy + Send + Sync>(value: T) -> T {
    value
}

#[trust_vc::ensures(result == value)]
fn concrete_copy_witness_caller_verified(value: CopyWitness) -> CopyWitness {
    copy_bound_identity_verified(value)
}

#[trust_vc::ensures(result == value)]
fn concrete_send_witness_caller_verified(value: SendSyncWitness) -> SendSyncWitness {
    send_bound_identity_verified(value)
}

#[trust_vc::ensures(result == value)]
fn concrete_sync_witness_caller_verified(value: SendSyncWitness) -> SendSyncWitness {
    sync_bound_identity_verified(value)
}

#[trust_vc::ensures(result == value)]
fn concrete_send_sync_witness_caller_verified(value: SendSyncWitness) -> SendSyncWitness {
    send_sync_where_bound_identity_verified(value)
}

#[trust_vc::ensures(result == value)]
fn shared_reference_lifetime_identity_verified<'a>(value: &'a u8) -> &'a u8 {
    value
}

#[trust_vc::ensures(true)]
fn copy_bound_false_assert_counterexample<T: Copy>(_value: T) {
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn send_bound_false_assert_counterexample<T: Send>(_value: T) {
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn sync_bound_false_assert_counterexample<T: Sync>(_value: T) {
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn send_sync_bound_false_assert_counterexample<T>(_value: T)
where
    T: Send + Sync,
{
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn copy_send_sync_bound_false_assert_counterexample<T: Copy + Send + Sync>(_value: T) {
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn phantom_data_marker_bound_currently_errors<T: Copy>(marker: std::marker::PhantomData<T>) {
    let _ = marker;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_raw_ptr_points_to_send_sync_currently_errors<T: Send + Sync>(
    value: vstd::raw_ptr::PointsTo<T>,
) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_raw_ptr_points_to_send_currently_errors<T: Send>(value: vstd::raw_ptr::PointsTo<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_raw_ptr_points_to_sync_currently_errors<T: Sync>(value: vstd::raw_ptr::PointsTo<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_cell_points_to_send_sync_currently_errors<T: Send + Sync>(value: vstd::cell::PointsTo<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_cell_points_to_send_currently_errors<T: Send>(value: vstd::cell::PointsTo<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_cell_points_to_sync_currently_errors<T: Sync>(value: vstd::cell::PointsTo<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_cell_pcell_send_sync_currently_errors<T: Send + Sync>(value: vstd::cell::pcell::PCell<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_tracked_marker_wrapper_currently_errors<T: Sync>(value: vstd::prelude::Tracked<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_ghost_marker_wrapper_currently_errors<T: Send + Sync>(value: vstd::prelude::Ghost<T>) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_local_invariant_marker_wrapper_currently_errors<T: Send>(
    value: vstd::invariant::LocalInvariant<(), T, Pred<(), T>>,
) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_atomic_invariant_marker_wrapper_currently_errors<T: Send>(
    value: vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>,
) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn vstd_atomic_invariant_send_sync_currently_errors<T: Send + Sync>(
    value: vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>,
) {
    let _ = value;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn copy_bound_const_generic_array_currently_errors<const N: usize, T: Copy>(_values: [T; N]) {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn dyn_send_marker_trait_object_currently_errors(_value: &dyn Send) {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn dyn_send_sync_marker_trait_object_currently_errors(_value: &(dyn Send + Sync)) {
    trust_vc::assert!(true);
}

struct Pred<A, B> {
    _a: A,
    _b: B,
}

struct Pred2;

#[trust_vc::ensures(true)]
fn vstd_tracked_covariant_shape_currently_errors<'a>(
    value: vstd::prelude::Tracked<&'static u8>,
) -> vstd::prelude::Tracked<&'a u8> {
    value
}

#[trust_vc::ensures(true)]
fn vstd_ghost_covariant_shape_currently_errors<'a>(
    value: vstd::prelude::Ghost<&'static u8>,
) -> vstd::prelude::Ghost<&'a u8> {
    value
}

#[trust_vc::ensures(true)]
fn vstd_local_invariant_variance_shape_currently_errors<'a>(
    value: vstd::invariant::LocalInvariant<(), &'static u8, Pred2>,
) -> vstd::invariant::LocalInvariant<(), &'a u8, Pred2> {
    value
}

#[trust_vc::ensures(true)]
fn vstd_atomic_invariant_variance_shape_currently_errors<'a>(
    value: vstd::invariant::AtomicInvariant<(), &'static u8, Pred2>,
) -> vstd::invariant::AtomicInvariant<(), &'a u8, Pred2> {
    value
}

#[trust_vc::ensures(true)]
fn rust_moved_value_marker_diagnostic_text_currently_errors() {
    debug_assert!(true, "use of moved value");
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rust_send_sync_marker_diagnostic_text_currently_errors() {
    debug_assert!(true, "between threads safely");
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn verus_variance_lifetime_marker_diagnostic_text_currently_errors() {
    debug_assert!(true, "lifetime may not live long enough");
    trust_vc::assert!(true);
}
