// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/core_special_setup.rs`.
//
// The upstream file verifies under Verus' `--is-core` setup with manual
// `verus_builtin`/`vstd` imports, collection equality helper macros, slice
// indexing over `x@`, and raw-pointer casts. TrustVc does not currently model
// that core-mode harness, Verus path attributes, or raw pointer metadata.
//
// This scout keeps the manifest entry unsupported-gap and records only stable,
// Rust-valid behavior TrustVc can execute today:
// - Seq/Set/Multiset equality assumptions used like the upstream equality
//   helper macros;
// - a fixed borrowed-array view/index witness adjacent to the upstream slice
//   indexing case;
// - a false Seq index assertion that produces a counterexample; and
// - a raw pointer cast-expression boundary that fails closed instead of
//   becoming corpus replacement evidence.

#![allow(dead_code)]

use trust_vc_types::{Multiset, Seq, Set, View};

pub type CoreSpecialSetupRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type CoreSpecialSetupRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CORE_SPECIAL_SETUP_RS_EXPECTED_CASES: &[CoreSpecialSetupRsExpectedCase] = &[
    (
        "core_special_setup_seq_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_set_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_multiset_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_slice_view_index_verified",
        "test_is_core",
        "verified",
        2,
    ),
    (
        "core_special_setup_seq_wrong_index_counterexample",
        "test_is_core",
        "counterexample",
        1,
    ),
    (
        "core_special_setup_raw_pointer_cast_currently_blocked",
        "test_is_core",
        "error",
        0,
    ),
];

pub const CORE_SPECIAL_SETUP_RS_FAIL_CLOSED_ERROR_PATTERNS: &[CoreSpecialSetupRsFailClosedErrorPatterns] =
    &[(
        "core_special_setup_raw_pointer_cast_currently_blocked",
        &["unsupported", "*mut", "cast"],
    )];

pub fn core_special_setup_rs_expected_cases() -> &'static [CoreSpecialSetupRsExpectedCase] {
    CORE_SPECIAL_SETUP_RS_EXPECTED_CASES
}

pub fn core_special_setup_rs_fail_closed_error_patterns(
) -> &'static [CoreSpecialSetupRsFailClosedErrorPatterns] {
    CORE_SPECIAL_SETUP_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::requires(a == b)]
#[trust_vc::ensures(true)]
fn core_special_setup_seq_equality_verified(a: Seq<i32>, b: Seq<i32>) {
    trust_vc::assert!(a == b);
}

#[trust_vc::requires(a == b)]
#[trust_vc::ensures(true)]
fn core_special_setup_set_equality_verified(a: Set<i32>, b: Set<i32>) {
    trust_vc::assert!(a == b);
}

#[trust_vc::requires(a == b)]
#[trust_vc::ensures(true)]
fn core_special_setup_multiset_equality_verified(a: Multiset<i32>, b: Multiset<i32>) {
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn core_special_setup_slice_view_index_verified() {
    let slice = &[9u8, 10u8];

    trust_vc::assert!(slice.view().len() == 2usize);
    trust_vc::assert!(slice.view().index(0usize) == 9u8);
}

#[trust_vc::ensures(true)]
fn core_special_setup_seq_wrong_index_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![1i32, 2i32].index(1usize) == 3i32);
}

#[trust_vc::ensures(true)]
fn core_special_setup_raw_pointer_cast_currently_blocked(addr: usize) {
    trust_vc::assert!(addr == (addr as *mut u8) as usize);
}
