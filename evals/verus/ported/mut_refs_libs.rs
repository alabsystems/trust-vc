// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_libs.rs`.
//
// The manifest entry may remain `unsupported-gap` while the director syncs the
// suite. This file carries schema-valid expected-case metadata instead of
// relying on manifest debt. Unknown outcomes are intentionally excluded.
//
// This file intentionally ports only Rust-valid, focused behavior from the
// upstream mutable-reference library tests:
// - executable runtime witnesses for Option::as_mut, Option slice views,
//   Option mutable slice views, and Option insert/get_or_insert
//   mutable-reference results, plus Vec index/field/nested update and
//   Vec-held mutable-reference update behavior;
// - TrustVc-verified Option Some/None and Option::as_mut(None) observation
//   prefixes shared by the upstream cases;
// - TrustVc-verified Vec::new/push and direct `vec![...]` scalar indexed-update
//   subsets adjacent to upstream Vec index assignment;
// - stable counterexamples on those prefixes and a Vec::new/push tuple-field
//   assignment false tail;
// - current fail-closed boundaries for library-returned mutable-reference
//   mutation, mutable slice writes, broader direct upstream `vec!` shapes, Vec
//   field/nested index mutation, index-out-of-bounds diagnostics,
//   Vec-held mutable references, and Verus-only `has_resolved`.
//
// Full parity still needs verification support for Option::as_mut(Some)
// mutable-reference mutation, Option::as_mut(None) source-Option preservation
// after the library call, Option::as_slice/as_mut_slice, Option::insert/
// get_or_insert, broader direct `vec!` literal modeling beyond scalar indexed
// assignment, tuple-field and nested Vec index assignment, Vec index mutable
// references, vectors of mutable references, Verus `has_resolved`, and
// index-out-of-bounds diagnostics.

#![allow(dead_code)]

pub type MutRefsLibsExpectedCase = (&'static str, &'static str, &'static str, usize);

struct MutRefsLibsPair {
    left: u64,
    right: u64,
}

struct MutRefsLibsTuplePair(u64, u64);

pub const MUT_REFS_LIBS_RS_EXPECTED_CASES: &[MutRefsLibsExpectedCase] = &[
    (
        "mut_refs_libs_option_some_none_prefix_verified",
        "test_option_as_mut_spec/test_options_as_mut_slice/test_option_insert_and_get_or_insert Option prefix",
        "verified",
        1,
    ),
    (
        "mut_refs_libs_option_as_mut_none_observation_verified",
        "test_option_as_mut_spec::test2 returned None observation prefix",
        "verified",
        1,
    ),
    (
        "mut_refs_libs_vec_push_index_assign_verified",
        "test_vec_index_assign::test Vec::new/push indexed assignment subset",
        "verified",
        5,
    ),
    (
        "mut_refs_libs_option_some_prefix_wrong_value_counterexample",
        "test_option_as_mut_spec wrong Some payload assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_option_as_mut_none_false_tail_counterexample",
        "test_option_as_mut_spec::test2_fails returned None observation prefix",
        "counterexample",
        2,
    ),
    (
        "mut_refs_libs_vec_push_index_assign_false_tail_counterexample",
        "test_vec_index_assign::fails Vec::new/push false-tail subset",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_option_as_mut_write_currently_blocked",
        "test_option_as_mut_spec::test1",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_write_false_tail_currently_blocked",
        "test_option_as_mut_spec::test1_fails",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_some_observation_currently_blocked",
        "test_option_as_mut_spec::test1 Option::as_mut(Some) observation prefix",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_none_source_option_currently_blocked",
        "test_option_as_mut_spec::test2 original Option remains None tail",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_slice_none_observation_currently_blocked",
        "test_options_as_mut_slice::test_as_slice_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_slice_some_observation_currently_blocked",
        "test_options_as_mut_slice::test_as_slice_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_slice_none_observation_currently_blocked",
        "test_options_as_mut_slice::test_as_mut_slice_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_slice_write_currently_blocked",
        "test_options_as_mut_slice::test_as_mut_slice_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_slice_none_false_tail_currently_blocked",
        "test_options_as_mut_slice::fail_as_slice_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_slice_some_false_tail_currently_blocked",
        "test_options_as_mut_slice::fail_as_slice_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_slice_none_false_tail_currently_blocked",
        "test_options_as_mut_slice::fail_as_mut_slice_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_as_mut_slice_write_false_tail_currently_blocked",
        "test_options_as_mut_slice::fail_as_mut_slice_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_mut_ref_currently_blocked",
        "test_option_insert_and_get_or_insert::test_insert_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_some_mut_ref_currently_blocked",
        "test_option_insert_and_get_or_insert::test_insert_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_none_mut_ref_currently_blocked",
        "test_option_insert_and_get_or_insert::test_get_or_insert_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_some_mut_ref_currently_blocked",
        "test_option_insert_and_get_or_insert::test_get_or_insert_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_none_result_observation_currently_blocked",
        "test_option_insert_and_get_or_insert::test_insert_none pre-mutation result observation",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_some_result_observation_currently_blocked",
        "test_option_insert_and_get_or_insert::test_insert_some pre-mutation result observation",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_none_result_observation_currently_blocked",
        "test_option_insert_and_get_or_insert::test_get_or_insert_none pre-mutation result observation",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_some_result_observation_currently_blocked",
        "test_option_insert_and_get_or_insert::test_get_or_insert_some pre-mutation result observation",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_none_false_tail_currently_blocked",
        "test_option_insert_and_get_or_insert::fail_insert_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_insert_some_false_tail_currently_blocked",
        "test_option_insert_and_get_or_insert::fail_insert_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_none_false_tail_currently_blocked",
        "test_option_insert_and_get_or_insert::fail_get_or_insert_none",
        "error",
        0,
    ),
    (
        "mut_refs_libs_option_get_or_insert_some_false_tail_currently_blocked",
        "test_option_insert_and_get_or_insert::fail_get_or_insert_some",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_assign_currently_blocked",
        "test_vec_index_assign::test",
        "verified",
        1,
    ),
    (
        "mut_refs_libs_vec_index_assign_false_tail_currently_blocked",
        "test_vec_index_assign::fails",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_vec_index_assign_fields_currently_blocked",
        "test_vec_index_assign::test_fields",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_vec_index_assign_fields_false_tail_currently_blocked",
        "test_vec_index_assign::fails_fields",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_vec_index_assign_nested_currently_blocked",
        "test_vec_index_assign::test_nested",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_assign_nested_false_tail_currently_blocked",
        "test_vec_index_assign::fails_nested",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_push_nested_index_assign_currently_blocked",
        "test_vec_index_assign::test_nested Vec::new/push nested assignment boundary",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_push_tuple_field_index_assign_false_tail_counterexample",
        "test_vec_index_assign::fails_fields Vec::new/push tuple-field assignment false tail",
        "counterexample",
        1,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_currently_blocked",
        "test_vec_index_mut_ref::test_mut_ref",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_false_tail_currently_blocked",
        "test_vec_index_mut_ref::fails_mut_ref",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_fields_currently_blocked",
        "test_vec_index_mut_ref::test_mut_ref_fields",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_fields_false_tail_currently_blocked",
        "test_vec_index_mut_ref::fails_mut_ref_fields",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_nested_currently_blocked",
        "test_vec_index_mut_ref::test_mut_ref_nested",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_mut_ref_nested_false_tail_currently_blocked",
        "test_vec_index_mut_ref::fails_mut_ref_nested",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_push_index_mut_ref_currently_blocked",
        "test_vec_index_mut_ref::test_mut_ref Vec::new/push mutable index reference boundary",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_assign_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds1",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_mut_ref_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds2",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_read_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds3",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_shared_ref_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds4",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_nested_assign_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds_nested",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_index_out_of_bounds_nested_mut_ref_currently_blocked",
        "test_index_out_of_bounds::test_out_of_bounds_nested2",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_of_mut_refs_currently_blocked",
        "test_vec_of_mut_refs::test_vec",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_of_mut_refs_false_tail_currently_blocked",
        "test_vec_of_mut_refs::fails_vec",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_of_mut_refs_reassign_currently_blocked",
        "test_vec_of_mut_refs::test_vec2",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_of_mut_refs_reassign_false_tail_currently_blocked",
        "test_vec_of_mut_refs::fails_vec2",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_push_of_mut_refs_currently_blocked",
        "test_vec_of_mut_refs::test_vec Vec::new/push mutable-reference element boundary",
        "error",
        0,
    ),
    (
        "mut_refs_libs_vec_of_mut_refs_has_resolved_currently_blocked",
        "test_vec_of_mut_refs has_resolved boundary",
        "error",
        0,
    ),
];

pub fn mut_refs_libs_rs_expected_cases() -> &'static [MutRefsLibsExpectedCase] {
    MUT_REFS_LIBS_RS_EXPECTED_CASES
}

pub fn mut_refs_libs_option_as_mut_runtime_some() {
    let mut opt = Some(5u64);
    let opt_ref_int = opt.as_mut();
    let ref_int = opt_ref_int.expect("Some value should yield a mutable reference");

    *ref_int = 20u64;

    assert_eq!(opt, Some(20u64));
}

pub fn mut_refs_libs_option_as_mut_runtime_none() {
    let mut opt = None::<u64>;
    let opt_ref_int = opt.as_mut();

    assert!(opt_ref_int.is_none());
    assert_eq!(opt, None::<u64>);
}

pub fn mut_refs_libs_option_as_slice_runtime_none() {
    let x = None::<u64>;
    let s = x.as_slice();

    assert!(s.is_empty());
    assert_eq!(x, None::<u64>);
}

pub fn mut_refs_libs_option_as_slice_runtime_some() {
    let x = Some(20u64);
    let s = x.as_slice();

    assert_eq!(s, &[20u64]);
    assert_eq!(x, Some(20u64));
}

pub fn mut_refs_libs_option_as_mut_slice_runtime_none() {
    let mut x = None::<u64>;
    let s = x.as_mut_slice();

    assert!(s.is_empty());
    assert!(x.is_none());
}

pub fn mut_refs_libs_option_as_mut_slice_runtime_some() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();

    assert_eq!(s, &[20u64]);
    s[0] = 30u64;

    assert_eq!(x, Some(30u64));
}

pub fn mut_refs_libs_option_insert_runtime_none() {
    let mut x = None::<u64>;
    let r = x.insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

pub fn mut_refs_libs_option_insert_runtime_some() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

pub fn mut_refs_libs_option_get_or_insert_runtime_none() {
    let mut x = None::<u64>;
    let r = x.get_or_insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

pub fn mut_refs_libs_option_get_or_insert_runtime_some() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);

    assert_eq!(*r, 5u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

pub fn mut_refs_libs_vec_index_assign_runtime_scalar() {
    let mut v = vec![1u64, 2u64, 3u64];

    v[1usize] = 5u64;

    assert_eq!(v, vec![1u64, 5u64, 3u64]);
    assert_eq!(v[2usize], 3u64);
}

pub fn mut_refs_libs_vec_index_assign_runtime_tuple_fields() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];

    v[1usize].0 = 5u64;

    assert_eq!(v[0usize].0, 1u64);
    assert_eq!(v[1usize].0, 5u64);
    assert_eq!(v[1usize].1, 12u64);
    assert_eq!(v[2usize].1, 13u64);
}

pub fn mut_refs_libs_vec_index_assign_runtime_fields() {
    let mut v = vec![
        MutRefsLibsPair {
            left: 1u64,
            right: 11u64,
        },
        MutRefsLibsPair {
            left: 2u64,
            right: 12u64,
        },
        MutRefsLibsPair {
            left: 3u64,
            right: 13u64,
        },
    ];

    v[1usize].left = 5u64;

    assert_eq!(v[0usize].left, 1u64);
    assert_eq!(v[1usize].left, 5u64);
    assert_eq!(v[1usize].right, 12u64);
    assert_eq!(v[2usize].right, 13u64);
}

pub fn mut_refs_libs_vec_index_assign_runtime_nested() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];

    v[1usize][1usize] = 15u64;

    assert_eq!(v[0usize], vec![1u64, 2u64, 3u64]);
    assert_eq!(v[1usize], vec![4u64, 15u64]);
    assert_eq!(v[2usize], vec![6u64]);
}

pub fn mut_refs_libs_vec_index_mut_ref_runtime_scalar() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1usize];

    *r = 5u64;

    assert_eq!(v, vec![1u64, 5u64, 3u64]);
    assert_eq!(v[2usize], 3u64);
}

pub fn mut_refs_libs_vec_index_mut_ref_runtime_tuple_fields() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    let r = &mut v[1usize].0;

    *r = 5u64;

    assert_eq!(v[0usize].0, 1u64);
    assert_eq!(v[1usize].0, 5u64);
    assert_eq!(v[1usize].1, 12u64);
    assert_eq!(v[2usize].1, 13u64);
}

pub fn mut_refs_libs_vec_index_mut_ref_runtime_fields() {
    let mut v = vec![
        MutRefsLibsPair {
            left: 1u64,
            right: 11u64,
        },
        MutRefsLibsPair {
            left: 2u64,
            right: 12u64,
        },
        MutRefsLibsPair {
            left: 3u64,
            right: 13u64,
        },
    ];
    let r = &mut v[1usize].left;

    *r = 5u64;

    assert_eq!(v[1usize].left, 5u64);
    assert_eq!(v[2usize].right, 13u64);
}

pub fn mut_refs_libs_vec_index_mut_ref_runtime_nested() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[1usize][1usize];

    *r = 15u64;

    assert_eq!(v[0usize], vec![1u64, 2u64, 3u64]);
    assert_eq!(v[1usize], vec![4u64, 15u64]);
    assert_eq!(v[2usize], vec![6u64]);
}

pub fn mut_refs_libs_vec_of_mut_refs_runtime_reassign() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0usize] = 10u64;
    *v[1usize] = 11u64;
    *v[2usize] = 12u64;

    v[2usize] = &mut d;
    *v[2usize] = 13u64;

    drop(v);

    assert_eq!(a, 10u64);
    assert_eq!(b, 11u64);
    assert_eq!(c, 12u64);
    assert_eq!(d, 13u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_some_none_prefix_verified() {
    let opt = Some(5u64);
    trust_vc::assert!(opt.is_some());
    trust_vc::assert!(opt.unwrap() == 5u64);

    let none = Option::<u64>::None;
    trust_vc::assert!(none.is_none());
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_some_prefix_wrong_value_counterexample() {
    let opt = Some(5u64);
    trust_vc::assert!(opt.is_some());
    trust_vc::assert!(opt.unwrap() == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_some_observation_currently_blocked() {
    let mut opt = Some(5u64);
    let opt_ref_int = opt.as_mut();

    trust_vc::assert!(opt_ref_int.is_some());
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_write_currently_blocked() {
    let mut opt = Some(5u64);
    let opt_ref_int = opt.as_mut();
    let ref_int = opt_ref_int.unwrap();

    *ref_int = 20u64;

    trust_vc::assert!(opt == Some(20u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_write_false_tail_currently_blocked() {
    let mut opt = Some(5u64);
    let opt_ref_int = opt.as_mut();
    let ref_int = opt_ref_int.unwrap();

    *ref_int = 20u64;

    trust_vc::assert!(opt == Some(20u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_none_observation_verified() {
    let mut opt = Option::<u64>::None;
    let opt_ref_int = opt.as_mut();

    trust_vc::assert!(opt_ref_int.is_none());
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_none_false_tail_counterexample() {
    let mut opt = Option::<u64>::None;
    let opt_ref_int = opt.as_mut();

    trust_vc::assert!(opt_ref_int.is_none());
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_none_source_option_currently_blocked() {
    let mut opt = Option::<u64>::None;
    let opt_ref_int = opt.as_mut();

    trust_vc::assert!(opt_ref_int.is_none());
    trust_vc::assert!(opt.is_none());
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_index_assign_verified() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    trust_vc::assert!(v.len() == 3usize);
    v[1usize] = 5u64;

    trust_vc::assert!(v.len() == 3usize);
    trust_vc::assert!(v[0usize] == 1u64);
    trust_vc::assert!(v[1usize] == 5u64);
    trust_vc::assert!(v[2usize] == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_index_assign_false_tail_counterexample() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    trust_vc::assert!(v.len() == 3usize);
    v[1usize] = 5u64;

    trust_vc::assert!(v.len() == 3usize);
    trust_vc::assert!(v[1usize] == 5u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_slice_none_observation_currently_blocked() {
    let x = Option::<u64>::None;
    let s = x.as_slice();

    trust_vc::assert!(s.len() == 0usize);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_slice_some_observation_currently_blocked() {
    let x = Some(20u64);
    let s = x.as_slice();

    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_slice_none_observation_currently_blocked() {
    let mut x = Option::<u64>::None;
    let s = x.as_mut_slice();

    trust_vc::assert!(s.len() == 0usize);
    trust_vc::assert!(x.is_none());
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_slice_write_currently_blocked() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();

    trust_vc::assert!(s.len() == 1usize);
    s[0] = 30u64;

    trust_vc::assert!(x == Some(30u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_slice_none_false_tail_currently_blocked() {
    let x = Option::<u64>::None;
    let s = x.as_slice();

    trust_vc::assert!(s.len() == 0usize);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_slice_some_false_tail_currently_blocked() {
    let x = Some(20u64);
    let s = x.as_slice();

    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == 20u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_slice_none_false_tail_currently_blocked() {
    let mut x = Option::<u64>::None;
    let s = x.as_mut_slice();

    trust_vc::assert!(s.len() == 0usize);
    trust_vc::assert!(x.is_none());
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_as_mut_slice_write_false_tail_currently_blocked() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();

    trust_vc::assert!(s.len() == 1usize);
    s[0] = 30u64;

    trust_vc::assert!(x == Some(30u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_mut_ref_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_some_mut_ref_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_none_mut_ref_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_some_mut_ref_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 5u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_none_result_observation_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_some_result_observation_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_none_result_observation_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_some_result_observation_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_none_false_tail_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_insert_some_false_tail_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_none_false_tail_currently_blocked() {
    let mut x = Option::<u64>::None;
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 20u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_option_get_or_insert_some_false_tail_currently_blocked() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);

    trust_vc::assert!(*r == 5u64);
    *r = 21u64;

    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];

    v[1] = 5u64;

    trust_vc::assert!(v[1] == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_false_tail_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];

    v[1] = 5u64;

    trust_vc::assert!(v[1] == 5u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_fields_currently_blocked() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];

    v[1].0 = 5u64;

    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[2].1 == 13u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_fields_false_tail_currently_blocked() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];

    v[1].0 = 5u64;

    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[2].1 == 13u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_nested_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];

    v[1][1] = 15u64;

    trust_vc::assert!(v[1][1] == 15u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_assign_nested_false_tail_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];

    v[1][1] = 15u64;

    trust_vc::assert!(v[1][1] == 15u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_nested_index_assign_currently_blocked() {
    let mut first: Vec<u64> = Vec::new();
    first.push(1u64);
    first.push(2u64);
    first.push(3u64);

    let mut second: Vec<u64> = Vec::new();
    second.push(4u64);
    second.push(5u64);

    let mut third: Vec<u64> = Vec::new();
    third.push(6u64);

    let mut v: Vec<Vec<u64>> = Vec::new();
    v.push(first);
    v.push(second);
    v.push(third);

    v[1usize][1usize] = 15u64;

    trust_vc::assert!(v[1usize][1usize] == 15u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_tuple_field_index_assign_false_tail_counterexample() {
    let mut v: Vec<MutRefsLibsTuplePair> = Vec::new();
    v.push(MutRefsLibsTuplePair(1u64, 11u64));
    v.push(MutRefsLibsTuplePair(2u64, 12u64));
    v.push(MutRefsLibsTuplePair(3u64, 13u64));

    v[1usize].0 = 5u64;

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1];

    *r = 5u64;

    trust_vc::assert!(v[1] == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_false_tail_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1];

    *r = 5u64;

    trust_vc::assert!(v[1] == 5u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_fields_currently_blocked() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    let r = &mut v[1].0;

    *r = 5u64;

    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[2].1 == 13u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_fields_false_tail_currently_blocked() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    let r = &mut v[1].0;

    *r = 5u64;

    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[2].1 == 13u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_nested_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[1][1];

    *r = 15u64;

    trust_vc::assert!(v[1][1] == 15u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_mut_ref_nested_false_tail_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[1][1];

    *r = 15u64;

    trust_vc::assert!(v[1][1] == 15u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_index_mut_ref_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);
    let r = &mut v[1usize];

    *r = 5u64;

    trust_vc::assert!(v[1usize] == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_assign_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];

    v[3] = 5u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_mut_ref_currently_blocked() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[3];

    *r = 5u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_read_currently_blocked() {
    let v = vec![1u64, 2u64, 3u64];
    let r = v[3];

    trust_vc::assert!(r == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_shared_ref_currently_blocked() {
    let v = vec![1u64, 2u64, 3u64];
    let r = &v[3];

    trust_vc::assert!(*r == 0u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_nested_assign_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];

    v[2][1] = 5u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_index_out_of_bounds_nested_mut_ref_currently_blocked() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[2][1];

    *r = 5u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_of_mut_refs_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0] = 10u64;

    trust_vc::assert!(*v[0] == 10u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_of_mut_refs_false_tail_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0] = 10u64;
    *v[1] = 11u64;
    *v[2] = 12u64;

    trust_vc::assert!(*v[0] == 10u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_of_mut_refs_reassign_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0] = 10u64;
    *v[1] = 11u64;
    *v[2] = 12u64;

    v[2] = &mut d;
    *v[2] = 13u64;

    trust_vc::assert!(*v[2] == 13u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_of_mut_refs_reassign_false_tail_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0] = 10u64;
    *v[1] = 11u64;
    *v[2] = 12u64;

    v[2] = &mut d;
    *v[2] = 13u64;

    trust_vc::assert!(*v[2] == 13u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_push_of_mut_refs_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut v: Vec<&mut u64> = Vec::new();
    v.push(&mut a);
    v.push(&mut b);
    v.push(&mut c);

    *v[0usize] = 10u64;

    trust_vc::assert!(*v[0usize] == 10u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_libs_vec_of_mut_refs_has_resolved_currently_blocked() {
    let mut a = 0u64;
    let r = &mut a;

    trust_vc::assert!(has_resolved(r));
}
