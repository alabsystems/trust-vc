// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/spec_derive.rs`.
//
// This file intentionally keeps the corpus manifest entry as `unsupported-gap`.
// The upstream file exercises `vstd::contrib::{make_spec_type, self_view}`
// proc macros, generated DeepView implementations, generated spec datatypes,
// macro input validation, excluded fields, lifetimes, enum variants, recursive
// rejection, and exact diagnostics. TrustVc does not yet model that macro
// surface directly.
//
// The Rust-valid scout below pins only stable behavior TrustVc can execute today:
// - manual struct-to-spec field projections for the basic `make_spec_type`
//   shape;
// - manual excluded-field projections mirroring the `exclude(y)` case;
// - manual identity projections for the `self_view` Copy case; and
// - a fail-closed HashMap field-view boundary from the complex deep-view case.

#![allow(dead_code, unused_imports, unused_variables)]

use std::collections::HashMap;
use trust_vc_types::View;

pub const SPEC_DERIVE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "make_spec_type_struct_manual_projection_verified",
        "test_basic_struct_make_spec_type",
        "verified",
        4,
    ),
    (
        "make_spec_type_exclude_field_manual_projection_verified",
        "test_complex_struct_with_exclude_and_lifetimes",
        "verified",
        2,
    ),
    (
        "self_view_copy_manual_identity_verified",
        "test_self_view_copy_works",
        "verified",
        2,
    ),
    (
        "make_spec_type_struct_wrong_projection_counterexample",
        "test_basic_struct_make_spec_type_false_adjacent_projection",
        "counterexample",
        1,
    ),
    (
        "make_spec_type_hash_map_field_view_fails_closed_error",
        "test_complex_struct_with_exclude_and_lifetimes",
        "error",
        0,
    ),
];

pub fn spec_derive_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SPEC_DERIVE_RS_EXPECTED_CASES
}

pub const SPEC_DERIVE_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "make_spec_type_hash_map_field_view_fails_closed_error",
    &["HashMap", "view"],
)];

pub fn spec_derive_rs_fail_closed_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    SPEC_DERIVE_RS_FAIL_CLOSED_ERROR_PATTERNS
}

struct TestStruct1 {
    x: u32,
    y: u32,
}

struct TestStruct1Spec {
    x: u32,
    y: u32,
}

struct TestStructWithExclude {
    x: u32,
    y: u32,
    z: u8,
}

struct TestStructWithExcludeSpec {
    x: u32,
    z: u8,
}

#[derive(Copy, Clone)]
struct CopyStruct {
    x: u32,
    y: i32,
}

struct StructWithHashMap {
    x: u32,
    u: HashMap<u32, u32>,
}

pub fn test_make_spec_type_manual_projection_runtime() {
    let original = TestStruct1 { x: 10, y: 20 };
    let spec = TestStruct1Spec {
        x: original.x,
        y: original.y,
    };

    assert_eq!(spec.x, 10);
    assert_eq!(spec.y, 20);
}

fn make_spec_type_struct_manual_projection_verified() {
    let original = TestStruct1 { x: 10u32, y: 20u32 };
    let spec = TestStruct1Spec {
        x: original.x,
        y: original.y,
    };

    trust_vc::assert!(spec.x == 10u32);
    trust_vc::assert!(spec.y == 20u32);
    trust_vc::assert!(original.x == spec.x);
    trust_vc::assert!(original.y == spec.y);
}

fn make_spec_type_exclude_field_manual_projection_verified() {
    let original = TestStructWithExclude {
        x: 42u32,
        y: 99u32,
        z: 7u8,
    };
    let spec = TestStructWithExcludeSpec {
        x: original.x,
        z: original.z,
    };

    let _excluded_y = original.y;
    trust_vc::assert!(spec.x == 42u32);
    trust_vc::assert!(spec.z == 7u8);
}

fn self_view_copy_manual_identity_verified() {
    let original = CopyStruct { x: 1u32, y: 2i32 };
    let view = original;

    trust_vc::assert!(view.x == original.x);
    trust_vc::assert!(view.y == original.y);
}

fn make_spec_type_struct_wrong_projection_counterexample() {
    let spec = TestStruct1Spec { x: 10u32, y: 20u32 };

    trust_vc::assert_by_compute!(
        spec.y == 21u32;
        compute_only
    );
}

fn make_spec_type_hash_map_field_view_fails_closed_error(original: StructWithHashMap) {
    trust_vc::assert!(original.u.view().contains_key(3u32) == original.u.view().contains_key(3u32));
}
