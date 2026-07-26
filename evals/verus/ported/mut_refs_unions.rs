// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_unions.rs`.
//
// The upstream file exercises Verus `new-mut-ref` reasoning over Rust unions:
// correct-variant field reads and writes, nested tuple-field projections,
// side-effect evaluation order, wrong-variant diagnostics, `is_variant`,
// `get_union_field`, `has_resolved`, and unions that store mutable references.
//
// TrustVc does not currently model Rust union active-variant state or unsafe
// union-field accesses. This scout therefore keeps the manifest entry
// `unsupported-gap` and records only stable evidence:
// - Rust-valid tagged-surrogate executable slices adjacent to the upstream
//   correct-variant union updates, mutable field borrows, and two-phase field
//   updates;
// - a struct-update-tail surrogate adjacent to upstream ctor_update_tail;
// - concrete stale-value and false-tail counterexamples after surrogate updates;
//   and
// - fail-closed native union, `is_variant`, `has_resolved`, and
//   `get_union_field` boundaries, including native struct-update-tail access.

#![allow(dead_code)]

#[derive(Clone, Copy, PartialEq, Eq)]
struct MutRefsUnionsPair {
    left: bool,
    right: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct MutRefsUnionsNumbers {
    e: u64,
    f: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct MutRefsUnionsTagged {
    active_a: bool,
    a: u64,
    b: MutRefsUnionsPair,
}

union MutRefsUnionsNative {
    a: u64,
    b: MutRefsUnionsPair,
}

pub const MUT_REFS_UNIONS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_unions_tagged_a_mut_ref_update_verified",
        "test_basic::test_mut_ref correct a-variant mut-ref field update surrogate",
        "verified",
        4,
    ),
    (
        "mut_refs_unions_tagged_a_field_update_verified",
        "test_basic::test_assign correct a-variant field update surrogate",
        "verified",
        3,
    ),
    (
        "mut_refs_unions_tagged_b_nested_mut_ref_update_verified",
        "test_basic::test_mut_ref_nested correct b-variant nested mut-ref update surrogate",
        "verified",
        4,
    ),
    (
        "mut_refs_unions_tagged_b_nested_update_verified",
        "test_basic::test_assign_nested correct b-variant nested update surrogate",
        "verified",
        4,
    ),
    (
        "mut_refs_unions_two_phase_scalar_update_verified",
        "two_phase_borrows_to_union_fields::test2 scalar field-ref update surrogate",
        "verified",
        4,
    ),
    (
        "mut_refs_unions_two_phase_struct_update_verified",
        "two_phase_borrows_to_union_fields2::test1 struct field update surrogate",
        "verified",
        4,
    ),
    (
        "mut_refs_unions_tagged_b_struct_update_tail_verified",
        "ctor_update_tail::test_update tagged b-variant struct-update-tail surrogate",
        "verified",
        2,
    ),
    (
        "mut_refs_unions_tagged_a_stale_value_counterexample",
        "test_basic::fails_assign stale a-field assertion surrogate",
        "counterexample",
        1,
    ),
    (
        "mut_refs_unions_tagged_b_struct_update_tail_counterexample",
        "ctor_update_tail::fails_update tagged b-variant false-tail surrogate",
        "counterexample",
        1,
    ),
    (
        "mut_refs_unions_native_field_access_currently_blocked",
        "test_basic::test_assign native union field access boundary",
        "error",
        0,
    ),
    (
        "mut_refs_unions_is_variant_currently_blocked",
        "two_phase_borrows_to_union_fields is_variant boundary",
        "error",
        0,
    ),
    (
        "mut_refs_unions_has_resolved_currently_blocked",
        "union_has_resolved::test native has_resolved boundary",
        "error",
        0,
    ),
    (
        "mut_refs_unions_get_union_field_currently_blocked",
        "two_phase_borrows_to_union_fields get_union_field boundary",
        "error",
        0,
    ),
    (
        "mut_refs_unions_native_struct_update_tail_wrong_variant_currently_blocked",
        "ctor_update_tail::wrong_variant native union struct-update-tail boundary",
        "error",
        0,
    ),
];

pub const MUT_REFS_UNIONS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "mut_refs_unions_native_field_access_currently_blocked",
        &["unsafe block", "unknown type", "unsupported"],
    ),
    (
        "mut_refs_unions_is_variant_currently_blocked",
        &["string literals are not yet supported", "is_variant"],
    ),
    (
        "mut_refs_unions_has_resolved_currently_blocked",
        &["has_resolved", "unknown return type for function"],
    ),
    (
        "mut_refs_unions_get_union_field_currently_blocked",
        &["string literals are not yet supported", "get_union_field"],
    ),
    (
        "mut_refs_unions_native_struct_update_tail_wrong_variant_currently_blocked",
        &["unsafe block", "unknown type", "unsupported"],
    ),
];

pub fn mut_refs_unions_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_UNIONS_RS_EXPECTED_CASES
}

pub fn mut_refs_unions_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MUT_REFS_UNIONS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_a_mut_ref_update_verified() {
    let active_a = true;
    let mut a = 5u64;
    let field_ref: &mut u64 = &mut a;

    *field_ref = 6u64;
    let y = a;

    trust_vc::assert!(active_a);
    trust_vc::assert!(y == 6u64);
    trust_vc::assert!(a == 6u64);
    trust_vc::assert!(*field_ref == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_a_field_update_verified() {
    let active_a = true;
    let mut a = 5u64;

    a = 6u64;
    let y = a;

    trust_vc::assert!(active_a);
    trust_vc::assert!(y == 6u64);
    trust_vc::assert!(a == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_b_nested_mut_ref_update_verified() {
    let active_a = false;
    let left = true;
    let mut right = false;
    let field_ref: &mut bool = &mut right;

    *field_ref = true;

    trust_vc::assert!(!active_a);
    trust_vc::assert!(left);
    trust_vc::assert!(right);
    trust_vc::assert!(*field_ref);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_b_nested_update_verified() {
    let active_a = false;
    let left = true;
    let mut right = false;

    right = true;

    trust_vc::assert!(!active_a);
    trust_vc::assert!(left);
    trust_vc::assert!(right);
    trust_vc::assert!(left && right);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_two_phase_scalar_update_verified() {
    let active_a = true;
    let mut a = 18u64;
    let field_ref: &mut u64 = &mut a;
    let next = *field_ref + 1u64;

    *field_ref = next;

    trust_vc::assert!(active_a);
    trust_vc::assert!(next == 19u64);
    trust_vc::assert!(a == 19u64);
    trust_vc::assert!(*field_ref == 19u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_two_phase_struct_update_verified() {
    let active_y = true;
    let mut y = MutRefsUnionsNumbers { e: 0u64, f: 1u64 };
    let y_ref: &mut MutRefsUnionsNumbers = &mut y;
    let new_e = y_ref.e + 10u64;

    y_ref.e = new_e;

    trust_vc::assert!(active_y);
    trust_vc::assert!(new_e == 10u64);
    trust_vc::assert!(y.e == 10u64);
    trust_vc::assert!(y.f == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_b_struct_update_tail_verified() {
    let source = MutRefsUnionsNumbers { e: 0u64, f: 1u64 };
    let updated = MutRefsUnionsNumbers { e: 10u64, ..source };

    trust_vc::assert!(updated.e == 10u64);
    trust_vc::assert!(updated.f == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_a_stale_value_counterexample() {
    let mut a = 5u64;

    a = 6u64;

    trust_vc::assert!(a == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_tagged_b_struct_update_tail_counterexample() {
    let source = MutRefsUnionsNumbers { e: 0u64, f: 1u64 };
    let updated = MutRefsUnionsNumbers { e: 10u64, ..source };

    trust_vc::assert!(updated.e == 10u64);
    trust_vc::assert!(updated.f == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_native_field_access_currently_blocked() {
    let mut x = MutRefsUnionsNative { a: 5u64 };

    x.a = 6u64;
    let y = unsafe { x.a };

    trust_vc::assert!(y == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_is_variant_currently_blocked(x: MutRefsUnionsNative) {
    trust_vc::assert!(is_variant(x, "a"));
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_has_resolved_currently_blocked(x: u64) {
    trust_vc::assert!(has_resolved(x));
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_get_union_field_currently_blocked(x: u64) {
    trust_vc::assert!(get_union_field::<MutRefsUnionsNative, u64>(x, "a") == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_unions_native_struct_update_tail_wrong_variant_currently_blocked() {
    let x = MutRefsUnionsNative { a: 3u64 };
    let updated = MutRefsUnionsPair {
        left: true,
        ..unsafe { x.b }
    };

    trust_vc::assert!(updated.left && updated.right);
}
