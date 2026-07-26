// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_slices_arrays.rs`.
//
// The upstream file is a `new-mut-ref` suite over boxed slices, unsized mutable
// slices, fixed arrays, nested array/slice projections, ref-mut match patterns,
// overflow diagnostics, and side-effect evaluation ordering. TrustVc does not
// currently mirror that whole Verus borrow/indexing model.
//
// This scout keeps the manifest entry as `unsupported-gap` and records only
// stable Rust-valid TrustVc evidence available today:
// - direct fixed-array indexed assignment and indexed assignment-op verify;
// - direct indexed assignment through `&mut [T; N]` and unsized `&mut [T]`
//   parameters verifies with explicit length/value preconditions, including
//   indexed assignment-op and tuple-field element mutation;
// - stale fixed-array, fixed-array mut-ref, unsized-slice mut-ref, assignment-op,
//   and false-tail assertions are rejected; and
// - boxed slices, mutable references to indexed array elements, nested
//   fixed-array reads,
//   ref-mut patterns, RHS/index side-effect ordering, array/slice
//   alias/unsizing surfaces, Verus-only resolvedness/history helpers, library
//   slice mutators, and side-effectful nested index reads remain fail-closed
//   unsupported boundaries.

#![allow(dead_code)]

pub const MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_slices_arrays_assign_array_verified",
        "array_basic::test_assign_array",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_verified",
        "array_basic::test_assign_mut_ref_array",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_verified",
        "slice_basic::test_assign_slice_mut_ref",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_verified",
        "control_flow_ordering3::test_assign_op direct fixed-array assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_verified",
        "array_basic direct fixed-array mutable-reference assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_verified",
        "slice_basic direct mutable-slice assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_array_index_currently_blocked",
        "array_basic::test_mut_ref_of_array_index",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_slice_index_currently_blocked",
        "slice_basic::test_mut_ref_of_slice_index",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_unsizing_coercion_currently_blocked",
        "mut_ref_unsizing_coercion::test",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_array stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_array_false_tail_counterexample",
        "array_basic::fail_assign_array false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_mut_ref_array stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_false_tail_counterexample",
        "array_basic::fail_assign_mut_ref_array false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_wrong_updated_value_counterexample",
        "slice_basic::fail_assign_slice_mut_ref stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_false_tail_counterexample",
        "slice_basic::fail_assign_slice_mut_ref false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_wrong_updated_value_counterexample",
        "control_flow_ordering3::fails_assign_op stale assignment-op value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_wrong_value_counterexample",
        "array_basic mutable-reference assignment-op stale value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_wrong_value_counterexample",
        "slice_basic mutable-slice assignment-op stale value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_nested_fixed_array_read_currently_rejected",
        "control_flow_ordering::test_read_1 non-side-effecting nested read",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_boxed_slice_assign_currently_blocked",
        "slice_basic::test_assign_slice_box",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_nested_currently_blocked",
        "array_basic::test_assign_mut_ref_array_nested",
        "verified",
        6,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_assign_mut_ref_slice_nested",
        "verified",
        6,
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_1",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_control_flow_temporary_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_2",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_currently_blocked",
        "control_flow_ordering3::test one-dimensional RHS-first assignment ordering",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_wrong_index_currently_blocked",
        "control_flow_ordering3::fails one-dimensional RHS-first stale-index assertion",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1 non-side-effecting nested indexed assignment target",
        "verified",
        2,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_add_assign_currently_blocked",
        "control_flow_ordering::test_assign_op_1 non-side-effecting nested indexed assignment-op target",
        "verified",
        2,
    ),
    (
        "mut_refs_slices_arrays_let_ref_mut_array_index_currently_blocked",
        "array_basic::test_let_decl_pattern_match_mut_ref_of_array_index",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_array_nested_currently_blocked",
        "array_basic::test_match_mut_ref_array_nested",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_match_mut_ref_slice_nested",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_array_of_mut_refs_currently_blocked",
        "array_of_mut_refs::test_array",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_of_mut_refs_currently_blocked",
        "slice_of_mut_refs::test_slice",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_has_resolved_in_index_expr_currently_blocked",
        "has_resolved_in_idx_expr::test1 has_resolved boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_final_len_currently_blocked",
        "mut_ref_to_slice_len_comparison::test final(a) length boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_old_indexed_slice_currently_blocked",
        "slice_index_then_field_1::upd old(a) indexed mutable-reference boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_first_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_first_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_last_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_last_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_currently_blocked",
        "slices_lib_split_at::test_split_at_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_end_currently_blocked",
        "slices_lib_split_at::test_split_at_mut_end",
        "error",
        0,
    ),
];

pub fn mut_refs_slices_arrays_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_array_verified() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];

    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_verified(x: &mut [u64; 3]) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_array_add_assign_verified() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];

    x[1usize] += 13u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_add_assign_verified(x: &mut [u64; 3]) {
    x[1usize] += 13u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_verified(x: &mut [u64]) {
    x[1usize] += 13u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_rhs_first_direct_assignment_currently_blocked() {
    let mut x: [u64; 2] = [0u64, 1u64];
    let mut a = 0usize;

    x[a] = {
        a = a + 1usize;
        5u64
    };

    trust_vc::assert!(x[0usize] == 0u64);
    trust_vc::assert!(x[1usize] == 5u64);
    trust_vc::assert!(a == 1usize);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_nested_fixed_array_read_currently_rejected() {
    let x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];
    let z = x[1usize][0usize];

    trust_vc::assert!(z == 2u64);
    trust_vc::assert!(x[0usize][1usize] == 1u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_array_wrong_updated_value_counterexample() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];

    x[1usize] = 20u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_array_false_tail_counterexample() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];

    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
    trust_vc::assert!(false);
}

#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_wrong_updated_value_counterexample(
    x: &mut [u64; 3],
) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_false_tail_counterexample(x: &mut [u64; 3]) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_boxed_slice_assign_currently_blocked(x: Box<[u64]>) {
    let mut x = x;

    x[1usize] = 20u64;

    trust_vc::assert!(x[1usize] == 20u64);
}

#[trust_vc::requires(x[0usize].0 == 5u64)]
#[trust_vc::requires(x[0usize].1 == 6u64)]
#[trust_vc::requires(x[1usize].0 == 7u64)]
#[trust_vc::requires(x[1usize].1 == 8u64)]
#[trust_vc::requires(x[2usize].0 == 9u64)]
#[trust_vc::requires(x[2usize].1 == 10u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_nested_currently_blocked(x: &mut [(u64, u64); 3]) {
    x[1usize].1 = 200u64;

    trust_vc::assert!(x[0usize].0 == 5u64);
    trust_vc::assert!(x[0usize].1 == 6u64);
    trust_vc::assert!(x[1usize].0 == 7u64);
    trust_vc::assert!(x[1usize].1 == 200u64);
    trust_vc::assert!(x[2usize].0 == 9u64);
    trust_vc::assert!(x[2usize].1 == 10u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_slice_mut_ref_verified(x: &mut [u64]) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_slice_mut_ref_wrong_updated_value_counterexample(x: &mut [u64]) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_slice_mut_ref_false_tail_counterexample(x: &mut [u64]) {
    x[1usize] = 20u64;

    trust_vc::assert!(x[0usize] == 5u64);
    trust_vc::assert!(x[1usize] == 20u64);
    trust_vc::assert!(x[2usize] == 8u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_array_add_assign_wrong_updated_value_counterexample() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];

    x[1usize] += 13u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_array_add_assign_wrong_value_counterexample(
    x: &mut [u64; 3],
) {
    x[1usize] += 13u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_wrong_value_counterexample(
    x: &mut [u64],
) {
    x[1usize] += 13u64;

    trust_vc::assert!(x[1usize] == 7u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize].0 == 5u64)]
#[trust_vc::requires(x[0usize].1 == 6u64)]
#[trust_vc::requires(x[1usize].0 == 7u64)]
#[trust_vc::requires(x[1usize].1 == 8u64)]
#[trust_vc::requires(x[2usize].0 == 9u64)]
#[trust_vc::requires(x[2usize].1 == 10u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_assign_mut_ref_slice_nested_currently_blocked(x: &mut [(u64, u64)]) {
    x[1usize].1 = 200u64;

    trust_vc::assert!(x[0usize].0 == 5u64);
    trust_vc::assert!(x[0usize].1 == 6u64);
    trust_vc::assert!(x[1usize].0 == 7u64);
    trust_vc::assert!(x[1usize].1 == 200u64);
    trust_vc::assert!(x[2usize].0 == 9u64);
    trust_vc::assert!(x[2usize].1 == 10u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_rhs_first_direct_assignment_wrong_index_currently_blocked() {
    let mut x: [u64; 2] = [0u64, 1u64];
    let mut a = 0usize;

    x[a] = {
        a = a + 1usize;
        5u64
    };

    trust_vc::assert!(x[0usize] == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_mut_ref_of_array_index_currently_blocked() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];
    let x_ref = &mut x[1usize];

    *x_ref = 20u64;

    trust_vc::assert!(x[1usize] == 20u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_mut_ref_of_slice_index_currently_blocked(x: &mut [u64]) {
    let x_ref = &mut x[1usize];

    *x_ref = 20u64;

    trust_vc::assert!(x[1usize] == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_control_flow_nested_index_assignment_currently_blocked() {
    let mut a = 0usize;
    let mut x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];

    x[{
        a = 10usize * a + 2usize;
        0usize
    }][{
        a = 10usize * a + 3usize;
        0usize
    }] = 5u64;

    trust_vc::assert!(x[0usize][0usize] == 5u64);
    trust_vc::assert!(a == 23usize);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_control_flow_nested_index_read_currently_blocked() {
    let mut a = 0usize;
    let x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];

    let z = x[{
        a = 10usize * a + 2usize;
        0usize
    }][{
        a = 10usize * a + 3usize;
        0usize
    }];

    trust_vc::assert!(z == 0u64);
    trust_vc::assert!(a == 23usize);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_control_flow_temporary_nested_index_read_currently_blocked() {
    let mut a = 0usize;
    let x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];

    let z = {
        a = 10usize * a + 1usize;
        x
    }[{
        a = 10usize * a + 2usize;
        0usize
    }][{
        a = 10usize * a + 3usize;
        0usize
    }];

    trust_vc::assert!(z == 0u64);
    trust_vc::assert!(a == 123usize);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_nested_array_index_assignment_currently_blocked() {
    let mut x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];

    x[0usize][0usize] = 5u64;

    trust_vc::assert!(x[0usize][0usize] == 5u64);
    trust_vc::assert!(x[1usize][1usize] == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_nested_array_index_add_assign_currently_blocked() {
    let mut x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]];

    x[0usize][0usize] += 5u64;

    trust_vc::assert!(x[0usize][0usize] == 5u64);
    trust_vc::assert!(x[1usize][1usize] == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_let_ref_mut_array_index_currently_blocked() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];
    let ref mut x_ref = x[1usize];

    *x_ref = 20u64;

    trust_vc::assert!(x[1usize] == 20u64);
}

#[trust_vc::requires(x[0usize].0 == 5u64)]
#[trust_vc::requires(x[0usize].1 == 6u64)]
#[trust_vc::requires(x[1usize].0 == 7u64)]
#[trust_vc::requires(x[1usize].1 == 8u64)]
#[trust_vc::requires(x[2usize].0 == 9u64)]
#[trust_vc::requires(x[2usize].1 == 10u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_match_mut_ref_array_nested_currently_blocked(x: &mut [(u64, u64); 3]) {
    match x[1usize] {
        (ref mut x_ref, ref mut y_ref) => {
            *x_ref = 20u64;
            *y_ref = 30u64;
        }
    }

    trust_vc::assert!(x[1usize].0 == 20u64);
    trust_vc::assert!(x[1usize].1 == 30u64);
}

#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize].0 == 5u64)]
#[trust_vc::requires(x[0usize].1 == 6u64)]
#[trust_vc::requires(x[1usize].0 == 7u64)]
#[trust_vc::requires(x[1usize].1 == 8u64)]
#[trust_vc::requires(x[2usize].0 == 9u64)]
#[trust_vc::requires(x[2usize].1 == 10u64)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_match_mut_ref_slice_nested_currently_blocked(x: &mut [(u64, u64)]) {
    match x[1usize] {
        (ref mut x_ref, ref mut y_ref) => {
            *x_ref = 20u64;
            *y_ref = 30u64;
        }
    }

    trust_vc::assert!(x[1usize].0 == 20u64);
    trust_vc::assert!(x[1usize].1 == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_mut_ref_unsizing_coercion_currently_blocked() {
    let mut a: [u64; 3] = [0u64, 1u64, 2u64];
    let a_ref: &mut [u64; 3] = &mut a;
    let a_ref2: &mut [u64] = a_ref;

    a_ref2[1usize] = 19u64;

    trust_vc::assert!(a[0usize] == 0u64);
    trust_vc::assert!(a[1usize] == 19u64);
    trust_vc::assert!(a[2usize] == 2u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_array_of_mut_refs_currently_blocked() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut x: [&mut u64; 3] = [&mut a, &mut b, &mut c];

    *x[0usize] = 10u64;
    *x[1usize] = 11u64;
    *x[2usize] = 12u64;

    x[2usize] = &mut d;
    *x[2usize] = 13u64;

    trust_vc::assert!(a == 10u64);
    trust_vc::assert!(b == 11u64);
    trust_vc::assert!(c == 12u64);
    trust_vc::assert!(d == 13u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_of_mut_refs_currently_blocked(x: Box<[&mut u64]>) {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut x = x;

    x[0usize] = &mut a;
    x[1usize] = &mut b;
    x[2usize] = &mut c;

    *x[0usize] = 10u64;
    *x[1usize] = 11u64;
    *x[2usize] = 12u64;

    x[2usize] = &mut d;
    *x[2usize] = 13u64;

    trust_vc::assert!(has_resolved(x[0usize]));
    trust_vc::assert!(has_resolved(x[1usize]));
    trust_vc::assert!(has_resolved(x[2usize]));
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_has_resolved_in_index_expr_currently_blocked() {
    let mut value = 0u64;
    let value_ref = &mut value;
    let mut values = [0u64, 1u64];

    values[{
        trust_vc::assert!(has_resolved(value_ref));
        0usize
    }] = 10u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_final_len_currently_blocked(x: &mut [u64]) {
    trust_vc::assert!(x.len() == final(x).len());
}

#[trust_vc::requires(x.len() > 0usize)]
#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_old_indexed_slice_currently_blocked(x: &mut [u64]) {
    x[0usize] = 20u64;

    trust_vc::assert!(old(x)[0usize] == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_first_mut_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let f = v.as_mut_slice().first_mut();
    let m = f.unwrap();
    *m = 10u64;

    trust_vc::assert!(v[0usize] == 10u64);
    trust_vc::assert!(v[1usize] == 2u64);
    trust_vc::assert!(v[2usize] == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_last_mut_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let f = v.as_mut_slice().last_mut();
    let m = f.unwrap();
    *m = 30u64;

    trust_vc::assert!(v[0usize] == 1u64);
    trust_vc::assert!(v[1usize] == 2u64);
    trust_vc::assert!(v[2usize] == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_split_at_mut_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let (a, b) = v.as_mut_slice().split_at_mut(2usize);
    a[1usize] = 20u64;
    b[0usize] = 30u64;

    trust_vc::assert!(v[0usize] == 1u64);
    trust_vc::assert!(v[1usize] == 20u64);
    trust_vc::assert!(v[2usize] == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_slices_arrays_slice_split_at_mut_end_currently_blocked() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);

    let (a, b) = v.as_mut_slice().split_at_mut(3usize);
    a[1usize] = 20u64;

    trust_vc::assert!(a[0usize] == 1u64);
    trust_vc::assert!(a[1usize] == 20u64);
    trust_vc::assert!(a[2usize] == 3u64);
    trust_vc::assert!(b.len() == 0usize);
}
