// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/slices.rs`.
//
// The upstream file covers Verus slice helpers, native indexing, generic
// indexing, Vec::as_slice, mutable slice updates, is_empty, recursive boxed
// slice type diagnostics, iterators, slice/array extensionality, std::ops::Index
// element/range implementations for slices, arrays, Vec, Arc<Vec>, and generic
// Index implementors. TrustVc does not currently mirror that full Verus slice
// model or diagnostic surface.
//
// This scout keeps the manifest entry as `unsupported-gap` and records only
// stable Rust-valid TrustVc evidence available today:
// - shared slice indexing from explicit length/value preconditions verifies;
// - fixed slice and array view length/index/contains/subrange witnesses verify;
// - direct mutable slice indexed assignment verifies under explicit length/value
//   preconditions;
// - wrong mutable-slice, view length/index, and subrange witnesses produce
//   counterexamples; and
// - direct Rust range indexing, std::ops::Index methods, Vec range indexing,
//   and mutable slice library helpers remain fail-closed.

#![allow(dead_code)]

use trust_vc_types::{Seq, View};

pub const SLICES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "slices_shared_index_from_requires_verified",
        "",
        "verified",
        1,
    ),
    (
        "slices_view_len_from_requires_verified",
        "",
        "verified",
        1,
    ),
    (
        "slices_literal_view_len_and_index_verified",
        "",
        "verified",
        2,
    ),
    (
        "slices_literal_view_contains_verified",
        "",
        "verified",
        3,
    ),
    (
        "slices_literal_view_subrange_verified",
        "",
        "verified",
        3,
    ),
    (
        "slices_array_view_len_index_contains_verified",
        "",
        "verified",
        4,
    ),
    (
        "slices_array_view_subrange_verified",
        "",
        "verified",
        3,
    ),
    (
        "slices_mut_index_assignment_verified",
        "",
        "verified",
        3,
    ),
    (
        "slices_mut_index_assignment_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_wrong_len_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_subrange_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_array_view_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_array_view_subrange_wrong_len_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_range_index_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_std_index_method_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_array_range_index_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_array_std_index_method_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_vec_range_index_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_vec_std_range_index_method_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_slice_first_mut_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "slices_slice_split_at_mut_currently_blocked",
        "",
        "error",
        0,
    ),
];

pub fn slices_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SLICES_RS_EXPECTED_CASES
}

pub const SLICES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "slices_range_index_currently_blocked",
        &["range", "unsupported", "index", "slice"],
    ),
    (
        "slices_std_index_method_currently_blocked",
        &["Index", "index", "unsupported", "method"],
    ),
    (
        "slices_array_range_index_currently_blocked",
        &["range", "unsupported", "index", "slice"],
    ),
    (
        "slices_array_std_index_method_currently_blocked",
        &["Index", "index", "unsupported", "method"],
    ),
    (
        "slices_vec_range_index_currently_blocked",
        &["range", "unsupported", "Vec", "index"],
    ),
    (
        "slices_vec_std_range_index_method_currently_blocked",
        &["Index", "range", "unsupported", "method"],
    ),
    (
        "slices_slice_first_mut_currently_blocked",
        &["first_mut", "unwrap", "unsupported", "mutable", "Vec"],
    ),
    (
        "slices_slice_split_at_mut_currently_blocked",
        &[
            "split_at_mut",
            "unsupported",
            "mutable",
            "Vec",
            "unresolved variable `v`",
        ],
    ),
];

pub fn slices_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    SLICES_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(x.len() == 2usize)]
#[trust_vc::requires(x[0usize] == 19u64)]
#[trust_vc::ensures(true)]
fn slices_shared_index_from_requires_verified(x: &[u64]) {
    let t = x[0usize];

    trust_vc::assert!(t == 19u64);
}

#[trust_vc::requires(x.len() == 4usize)]
#[trust_vc::ensures(true)]
fn slices_view_len_from_requires_verified(x: &[u8]) {
    trust_vc::assert!(x.view().len() == 4usize);
}

#[trust_vc::ensures(true)]
fn slices_literal_view_len_and_index_verified() {
    let slice = &[0u8, 2u8, 4u8];

    trust_vc::assert!(slice.view().len() == 3usize);
    trust_vc::assert!(slice.view().index(2usize) == 4u8);
}

#[trust_vc::ensures(true)]
fn slices_literal_view_contains_verified() {
    let slice = &[0u8, 2u8, 4u8];

    trust_vc::assert!(slice.view().contains(0u8));
    trust_vc::assert!(slice.view().contains(4u8));
    trust_vc::assert!(!slice.view().contains(5u8));
}

#[trust_vc::ensures(true)]
fn slices_literal_view_subrange_verified() {
    let slice = &[10u8, 20u8, 30u8, 40u8];
    let mid: Seq<u8> = slice.view().subrange(1usize, 3usize);

    trust_vc::assert!(mid.len() == 2usize);
    trust_vc::assert!(mid.index(0usize) == 20u8);
    trust_vc::assert!(mid.index(1usize) == 30u8);
}

#[trust_vc::ensures(true)]
fn slices_array_view_len_index_contains_verified() {
    let array = [1u8, 3u8, 5u8, 7u8, 9u8];

    trust_vc::assert!(array.view().len() == 5usize);
    trust_vc::assert!(array.view().index(2usize) == 5u8);
    trust_vc::assert!(array.view().contains(7u8));
    trust_vc::assert!(!array.view().contains(8u8));
}

#[trust_vc::ensures(true)]
fn slices_array_view_subrange_verified() {
    let array = [1u8, 3u8, 5u8, 7u8, 9u8];
    let mid: Seq<u8> = array.view().subrange(1usize, 4usize);

    trust_vc::assert!(mid.len() == 3usize);
    trust_vc::assert!(mid.index(0usize) == 3u8);
    trust_vc::assert!(mid.index(2usize) == 7u8);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn slices_mut_index_assignment_verified(x: &mut [u64]) {
    x[0usize] = 5u64;
    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::ensures(true)]
fn slices_mut_index_assignment_wrong_value_counterexample(x: &mut [u64]) {
    x[0usize] = 5u64;

    trust_vc::assert!(x[0usize] == 7u64);
}

#[trust_vc::ensures(true)]
fn slices_literal_view_wrong_len_counterexample() {
    let slice = &[0u8, 2u8, 4u8];

    trust_vc::assert!(slice.view().len() == 4usize);
}

#[trust_vc::ensures(true)]
fn slices_literal_view_wrong_index_counterexample() {
    let slice = &[0u8, 2u8, 4u8];

    trust_vc::assert!(slice.view().index(1usize) == 4u8);
}

#[trust_vc::ensures(true)]
fn slices_literal_view_subrange_wrong_index_counterexample() {
    let slice = &[10u8, 20u8, 30u8, 40u8];
    let mid: Seq<u8> = slice.view().subrange(1usize, 3usize);

    trust_vc::assert!(mid.index(1usize) == 40u8);
}

#[trust_vc::ensures(true)]
fn slices_array_view_wrong_index_counterexample() {
    let array = [1u8, 3u8, 5u8, 7u8, 9u8];

    trust_vc::assert!(array.view().index(2usize) == 7u8);
}

#[trust_vc::ensures(true)]
fn slices_array_view_subrange_wrong_len_counterexample() {
    let array = [1u8, 3u8, 5u8, 7u8, 9u8];
    let mid: Seq<u8> = array.view().subrange(1usize, 4usize);

    trust_vc::assert!(mid.len() == 2usize);
}

#[trust_vc::requires(x.len() == 5usize)]
#[trust_vc::ensures(true)]
fn slices_range_index_currently_blocked(x: &[u8]) {
    let sub = &x[1usize..3usize];

    trust_vc::assert!(sub.len() == 2usize);
}

#[trust_vc::requires(x.len() == 5usize)]
#[trust_vc::ensures(true)]
fn slices_std_index_method_currently_blocked(x: &[u8]) {
    use std::ops::Index;

    let t = *x.index(2usize);

    trust_vc::assert!(t == x[2usize]);
}

#[trust_vc::ensures(true)]
fn slices_array_range_index_currently_blocked(x: &[u8; 5]) {
    let sub = &x[1usize..3usize];

    trust_vc::assert!(sub.len() == 2usize);
}

#[trust_vc::ensures(true)]
fn slices_array_std_index_method_currently_blocked(x: &[u8; 5]) {
    use std::ops::Index;

    let t = *x.index(2usize);

    trust_vc::assert!(t == x[2usize]);
}

#[trust_vc::requires(x.len() == 5usize)]
#[trust_vc::ensures(true)]
fn slices_vec_range_index_currently_blocked(x: &Vec<u8>) {
    let sub = &x[1usize..3usize];

    trust_vc::assert!(sub.len() == 2usize);
}

#[trust_vc::requires(x.len() == 5usize)]
#[trust_vc::ensures(true)]
fn slices_vec_std_range_index_method_currently_blocked(x: &Vec<u8>) {
    use std::ops::Index;

    let sub = x.index(1usize..3usize);

    trust_vc::assert!(sub.len() == 2usize);
}

#[trust_vc::ensures(true)]
fn slices_slice_first_mut_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let first = v.as_mut_slice().first_mut();
    let first = first.unwrap();
    *first = 10u64;

    trust_vc::assert!(v[0usize] == 10u64);
    trust_vc::assert!(v[1usize] == 2u64);
    trust_vc::assert!(v[2usize] == 3u64);
}

#[trust_vc::ensures(true)]
fn slices_slice_split_at_mut_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let (left, right) = v.as_mut_slice().split_at_mut(2usize);
    left[1usize] = 20u64;
    right[0usize] = 30u64;

    trust_vc::assert!(v[0usize] == 1u64);
    trust_vc::assert!(v[1usize] == 20u64);
    trust_vc::assert!(v[2usize] == 30u64);
}
