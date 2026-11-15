// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial TrustVc port for upstream Verus `rust_verify_test/tests/arrays.rs`.
//
// This covers only native fixed-size array type parsing, array indexing, array
// `.view().len()`, array literals including concrete parameter arrays, literal
// repeat arrays including concrete Copy parameter repeats, direct indexed
// assignment and indexed compound assignment on repeat and literal arrays and
// fixed array parameters including copied parameter locals and upstream
// `test1::test9` copied owned/borrowed struct-field array locals and direct
// owned struct-field array shapes, a narrow direct and dependent-index fixed-size
// `&mut [T; N]` update subset including the upstream
// `test_array_set` shape, stable false-tail counterexamples for array-view
// surfaces, a local pre-state snapshot readback for a direct `&mut` indexed
// assignment, array cloning, array literal
// equality/inequality including the upstream named-local array shape, literal
// array-to-Seq conversion, Seq binding `.contains(...)` and inequality
// witnesses from array views, selected array-to-slice len/index/contains
// probes, and a stable scalar counterexample. The manifest keeps the upstream
// file fail-closed because const generics, tracked diagnostics, non-Copy repeat
// diagnostics, recursion checks, spec-fn array literals, generic array indexing
// helpers, source-level `&mut` array old-state postconditions, borrowed array
// aliases, projection indexed assignment beyond direct owned struct fields,
// side-effecting indexed assignment ops, boxed array-to-slice coercions, and
// solver-unknown negative array-view/index facts are not fully mirrored.

#![allow(dead_code)]

use trust_vc_types::{Seq, View};

pub type ArraysRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ArraysRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ARRAYS_RS_EXPECTED_CASES: &[ArraysRsExpectedCase] = &[
    ("array_index_from_requires", "test1", "verified", 2),
    ("array_view_len_from_fixed_type", "test1", "verified", 1),
    (
        "array_literal_view_values",
        "test_array_literals",
        "verified",
        3,
    ),
    (
        "array_literal_named_view_values_exact",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_concrete_param_view_values",
        "test_array_literals",
        "verified",
        1,
    ),
    ("array_repeat_view_values", "test_array_repeat", "verified", 3),
    (
        "array_repeat_named_view_values_exact",
        "test_array_repeat",
        "verified",
        1,
    ),
    (
        "array_repeat_concrete_param_view_values",
        "test_array_repeat",
        "verified",
        1,
    ),
    (
        "array_literal_six_view_values_exact",
        "test_array_literals",
        "verified",
        6,
    ),
    (
        "array_repeat_six_view_values_exact",
        "test_array_repeat",
        "verified",
        6,
    ),
    (
        "array_clone_repeat_literal",
        "test_array_clone",
        "verified",
        1,
    ),
    ("array_index_assignment_repeat_literal", "test1", "verified", 1),
    (
        "array_parenthesized_index_assignment_repeat_literal",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_pair_literal_exact",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_param_array",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_struct_field_array",
        "test1",
        "verified",
        2,
    ),
    (
        "array_index_add_assign_repeat_literal",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_parenthesized_index_add_assign_repeat_literal",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_mul_assign_binary_rhs_precedence",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_param_array",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_param_array",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_assign_mut_ref_local_snapshot",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_assign_mut_ref_usize_twenty",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_dependent_index",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_set_mut_ref_u8_twenty",
        "test_array_set",
        "verified",
        1,
    ),
    (
        "array_to_slice_view_len_and_index",
        "test_array_to_slice",
        "verified",
        2,
    ),
    (
        "array_to_slice_ref_view_len_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_ref_coercion_view_len_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_literal_view_len_and_index_exact",
        "test_array_to_slice",
        "verified",
        2,
    ),
    (
        "array_to_slice_local_ref_coercion_view_len_and_index_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_literal_view_contains_exact",
        "test_array_to_slice",
        "verified",
        3,
    ),
    (
        "array_literal_inequality",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_to_seq_index",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_to_seq_inequality",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_view_to_seq_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_named_inequality_and_contains",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_view_seq_binding_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_seq_binding_reuse",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_named_view_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_index_assign_local_snapshot_wrong_value_counterexample",
        "test_array_set_assign_op",
        "counterexample",
        1,
    ),
    (
        "array_to_slice_literal_view_false_tail_counterexample",
        "test_array_to_slice",
        "counterexample",
        1,
    ),
    (
        "array_literal_view_seq_binding_false_tail_counterexample",
        "test_array_literals",
        "counterexample",
        1,
    ),
    (
        "array_named_view_contains_false_tail_counterexample",
        "test_array_literals",
        "counterexample",
        1,
    ),
    (
        "array_const_generic_view_len_currently_blocked",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_old_state_currently_blocked",
        "test_array_set_assign_op",
        "error",
        0,
    ),
    (
        "array_index_add_assign_mut_ref_alias_currently_blocked",
        "test_array_set_assign_op",
        "error",
        0,
    ),
    (
        "array_index_assignment_struct_field_target_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_borrowed_struct_field_array",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_side_effect_index_currently_blocked",
        "test_array_set_assign_op_with_idx_side_effect",
        "error",
        0,
    ),
    // RE-PINNED 2026-09-13: four false array-view claims that were parked as
    // "currently unknown" scouts (referenced by neither the suite nor the
    // manifest) are refuted with a model by the engine and are pinned as
    // Counterexamples beside their verified twins.
    (
        "array_to_slice_literal_view_wrong_contains_counterexample",
        "test_array_to_slice",
        "counterexample",
        2,
    ),
    (
        "array_to_slice_wrong_len_counterexample",
        "test_array_to_slice",
        "counterexample",
        2,
    ),
    (
        "array_literal_view_seq_binding_wrong_contains_counterexample",
        "test_array_literals",
        "counterexample",
        2,
    ),
    (
        "array_named_view_wrong_contains_counterexample",
        "test_array_literals",
        "counterexample",
        2,
    ),
];

pub const ARRAYS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ArraysRsFailClosedErrorPatterns] = &[
    (
        "array_index_add_assign_mut_ref_old_state_currently_blocked",
        &[
            "Unsupported old-state expression `old(...)`",
            "array/reference places",
            "current state as pre-state",
        ],
    ),
    (
        "array_index_add_assign_mut_ref_alias_currently_blocked",
        &[
            "indexed assignment through a borrowed array/reference alias",
            "aliased state as an independent array",
        ],
    ),
    (
        "array_index_add_assign_side_effect_index_currently_blocked",
        &[
            "unsupported expression",
            "&mut not supported",
            "side-effect-free",
        ],
    ),
];

pub fn arrays_rs_expected_cases() -> &'static [ArraysRsExpectedCase] {
    ARRAYS_RS_EXPECTED_CASES
}

pub fn arrays_rs_fail_closed_error_patterns() -> &'static [ArraysRsFailClosedErrorPatterns] {
    ARRAYS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::requires(ar[1usize] == 19u8)]
#[trust_vc::ensures(true)]
fn array_index_from_requires(ar: [u8; 20]) {
    trust_vc::assert!(ar[1usize] == 19u8);
}

#[trust_vc::ensures(true)]
fn array_view_len_from_fixed_type(ar: [u8; 20]) {
    trust_vc::assert!(ar.view().len() == 20usize);
}

#[trust_vc::ensures(true)]
fn array_literal_view_values() {
    trust_vc::assert!([11u8, 12u8, 13u8].view().len() == 3usize);
    trust_vc::assert!([11u8, 12u8, 13u8].view().index(0usize) == 11u8);
    trust_vc::assert!([11u8, 12u8, 13u8].view().index(2usize) == 13u8);
}

#[trust_vc::ensures(true)]
fn array_literal_named_view_values_exact() {
    let x: [u8; 6] = [11u8, 12u8, 13u8, 14u8, 15u8, 16u8];
    trust_vc::assert!(x.view().len() == 6usize);
    trust_vc::assert!(x.view().index(0usize) == 11u8);
    trust_vc::assert!(x.view().index(1usize) == 12u8);
    trust_vc::assert!(x.view().index(2usize) == 13u8);
    trust_vc::assert!(x.view().index(3usize) == 14u8);
    trust_vc::assert!(x.view().index(4usize) == 15u8);
    trust_vc::assert!(x.view().index(5usize) == 16u8);
}

#[trust_vc::ensures(true)]
fn array_literal_concrete_param_view_values(a: u8, b: u8, c: u8) {
    let x: [u8; 3] = [a, b, c];
    trust_vc::assert!(x.view().len() == 3usize);
    trust_vc::assert!(x.view().index(0usize) == a);
    trust_vc::assert!(x.view().index(1usize) == b);
    trust_vc::assert!(x.view().index(2usize) == c);
}

#[trust_vc::ensures(true)]
fn array_repeat_view_values() {
    trust_vc::assert!([11u8; 3].view().len() == 3usize);
    trust_vc::assert!([11u8; 3].view().index(0usize) == 11u8);
    trust_vc::assert!([11u8; 3].view().index(2usize) == 11u8);
}

#[trust_vc::ensures(true)]
fn array_repeat_named_view_values_exact() {
    let x: [u8; 6] = [11u8; 6];
    trust_vc::assert!(x.view().len() == 6usize);
    trust_vc::assert!(x.view().index(0usize) == 11u8);
    trust_vc::assert!(x.view().index(1usize) == 11u8);
    trust_vc::assert!(x.view().index(2usize) == 11u8);
    trust_vc::assert!(x.view().index(3usize) == 11u8);
    trust_vc::assert!(x.view().index(4usize) == 11u8);
    trust_vc::assert!(x.view().index(5usize) == 11u8);
}

#[trust_vc::ensures(true)]
fn array_repeat_concrete_param_view_values(a: u8) {
    let x: [u8; 3] = [a; 3];
    trust_vc::assert!(x.view().len() == 3usize);
    trust_vc::assert!(x.view().index(0usize) == a);
    trust_vc::assert!(x.view().index(1usize) == a);
    trust_vc::assert!(x.view().index(2usize) == a);
}

#[trust_vc::ensures(true)]
fn array_literal_six_view_values_exact() {
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().len() == 6usize);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(0usize) == 11u8);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(1usize) == 12u8);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(2usize) == 13u8);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(3usize) == 14u8);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(4usize) == 15u8);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(5usize) == 16u8);
}

#[trust_vc::ensures(true)]
fn array_repeat_six_view_values_exact() {
    trust_vc::assert!([11u8; 6].view().len() == 6usize);
    trust_vc::assert!([11u8; 6].view().index(0usize) == 11u8);
    trust_vc::assert!([11u8; 6].view().index(1usize) == 11u8);
    trust_vc::assert!([11u8; 6].view().index(2usize) == 11u8);
    trust_vc::assert!([11u8; 6].view().index(3usize) == 11u8);
    trust_vc::assert!([11u8; 6].view().index(4usize) == 11u8);
    trust_vc::assert!([11u8; 6].view().index(5usize) == 11u8);
}

#[trust_vc::ensures(true)]
fn array_clone_repeat_literal() {
    let a = [0u8; 16];
    let _b = a.clone();
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_repeat_literal() {
    let mut a = [0u8; 3];
    a[1usize] = 9u8;
    assert!(a[1usize] == 9u8);
    assert!(a[0usize] == 0u8);
    assert!(a[2usize] == 0u8);
}

#[trust_vc::ensures(true)]
fn array_parenthesized_index_assignment_repeat_literal() {
    let mut a = [0u8; 3];
    (a[1usize]) = 9u8;
    assert!(a[1usize] == 9u8);
    assert!(a[0usize] == 0u8);
    assert!(a[2usize] == 0u8);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_pair_literal_exact() {
    let mut ar = [0usize, 0usize];
    assert!(ar[0usize] == 0usize);
    ar[0usize] = 42usize;
    assert!(ar[0usize] == 42usize);
    assert!(ar[1usize] == 0usize);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_copied_param_array(ar: [u8; 20]) {
    let mut ar = ar;
    ar[7usize] = 50u8;
    assert!(ar[7usize] == 50u8);
}

struct ArrayFieldHolder {
    ar: [usize; 4],
}

#[trust_vc::requires(s.ar[1usize] == 9usize)]
#[trust_vc::ensures(true)]
fn array_index_assignment_copied_struct_field_array(s: ArrayFieldHolder) {
    let mut ar = s.ar;
    ar[0usize] = 42usize;
    assert!(ar[0usize] == 42usize);
    assert!(ar[1usize] == 9usize);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_copied_borrowed_struct_field_array(s: &mut ArrayFieldHolder) {
    let mut ar = s.ar;
    ar[0usize] = 42usize;
    assert!(ar[0usize] == 42usize);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_struct_field_target_verified(mut s: ArrayFieldHolder) {
    s.ar[0usize] = 42usize;
    assert!(s.ar[0usize] == 42usize);
}

#[trust_vc::ensures(true)]
fn array_index_assignment_wrong_other_value_counterexample() {
    let mut a = [0u8; 3];
    a[1usize] = 9u8;
    assert!(a[0usize] == 9u8);
}

#[trust_vc::ensures(true)]
fn array_index_add_assign_repeat_literal() {
    let mut a = [0u8; 3];
    a[1usize] += 1u8;
    assert!(a[1usize] == 1u8);
    assert!(a[0usize] == 0u8);
    assert!(a[2usize] == 0u8);
}

#[trust_vc::ensures(true)]
fn array_parenthesized_index_add_assign_repeat_literal() {
    let mut a = [0u8; 3];
    (a[1usize]) += 1u8;
    assert!(a[1usize] == 1u8);
    assert!(a[0usize] == 0u8);
    assert!(a[2usize] == 0u8);
}

#[trust_vc::ensures(true)]
fn array_index_mul_assign_binary_rhs_precedence() {
    let mut a = [2u8; 3];
    let b = 3u8;
    let c = 4u8;
    a[1usize] *= b + c;
    assert!(a[1usize] == 14u8);
    assert!(a[0usize] == 2u8);
    assert!(a[2usize] == 2u8);
}

#[trust_vc::requires(ar[0usize] == 7u8)]
#[trust_vc::requires(ar[1usize] == 4u8)]
#[trust_vc::requires(ar[2usize] == 8u8)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_param_array(mut ar: [u8; 3]) {
    ar[1usize] += 1u8;
    assert!(ar[1usize] == 5u8);
    assert!(ar[0usize] == 7u8);
    assert!(ar[2usize] == 8u8);
}

#[trust_vc::requires(ar[0usize] == 7u8)]
#[trust_vc::requires(ar[1usize] == 4u8)]
#[trust_vc::requires(ar[2usize] == 8u8)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_param_array(ar: &mut [u8; 3]) {
    ar[1usize] += 1u8;
    assert!(ar[1usize] == 5u8);
    assert!(ar[0usize] == 7u8);
    assert!(ar[2usize] == 8u8);
}

#[trust_vc::requires(ar[0usize] == 7u8)]
#[trust_vc::requires(ar[1usize] == 4u8)]
#[trust_vc::requires(ar[2usize] == 8u8)]
#[trust_vc::ensures(true)]
fn array_index_assign_mut_ref_local_snapshot(ar: &mut [u8; 3]) {
    let before = ar[1usize];
    ar[1usize] = before + 1u8;
    assert!(before == 4u8);
    assert!(ar[1usize] == before + 1u8);
    assert!(ar[0usize] == 7u8);
    assert!(ar[2usize] == 8u8);
}

#[trust_vc::requires(ar[0usize] == 11usize)]
#[trust_vc::requires(ar[17usize] == 5usize)]
#[trust_vc::ensures(true)]
fn array_index_assign_mut_ref_usize_twenty(ar: &mut [usize; 20]) {
    ar[17usize] = 42usize;
    assert!(ar[17usize] == 42usize);
    assert!(ar[0usize] == 11usize);
}

#[trust_vc::requires(ar[0usize] == 1usize)]
#[trust_vc::requires(ar[2usize] == 2usize)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_dependent_index(ar: &mut [usize; 20]) {
    ar[0usize] += 1usize;
    ar[ar[0usize]] += 1usize;
    assert!(ar[0usize] == 2usize);
    assert!(ar[2usize] == 3usize);
}

#[trust_vc::requires(ar[2usize] == 7u8)]
#[trust_vc::ensures(true)]
fn array_index_set_mut_ref_u8_twenty(ar: &mut [u8; 20]) {
    ar[0usize] = 1u8;
    assert!(ar[0usize] == 1u8);
    assert!(ar[2usize] == 7u8);
}

#[trust_vc::ensures(true)]
fn array_index_add_assign_wrong_updated_value_counterexample() {
    let mut a = [0u8; 3];
    a[1usize] += 1u8;
    assert!(a[1usize] == 0u8);
}

#[trust_vc::requires(ar[1usize] == 4u8)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_wrong_updated_value_counterexample(ar: &mut [u8; 3]) {
    ar[1usize] += 1u8;
    assert!(ar[1usize] == 4u8);
}

#[trust_vc::ensures(true)]
fn array_index_assign_local_snapshot_wrong_value_counterexample() {
    let mut a = [7u8, 4u8, 8u8];
    let before = 4u8;
    a[1usize] = before + 1u8;
    assert!(before == 5u8);
}

#[trust_vc::requires(ar[0usize] == 1usize)]
#[trust_vc::requires(ar[2usize] == 2usize)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_dependent_index_wrong_value_counterexample(ar: &mut [usize; 20]) {
    ar[0usize] += 1usize;
    ar[ar[0usize]] += 1usize;
    assert!(ar[1usize] == 3usize);
}

#[trust_vc::ensures(true)]
fn array_index_set_mut_ref_wrong_value_counterexample(ar: &mut [u8; 20]) {
    ar[0usize] = 1u8;
    assert!(ar[0usize] == 2u8);
}

#[trust_vc::ensures(true)]
fn array_index_add_assign_wrong_other_value_counterexample() {
    let mut a = [0u8; 3];
    a[1usize] += 1u8;
    assert!(a[0usize] == 1u8);
}

#[trust_vc::ensures(true)]
fn array_index_mul_assign_binary_rhs_wrong_precedence_counterexample() {
    let mut a = [2u8; 3];
    let b = 3u8;
    let c = 4u8;
    a[1usize] *= b + c;
    assert!(a[1usize] == 10u8);
}

#[trust_vc::requires(ar[1usize] == 5u8)]
#[trust_vc::ensures(true)]
fn array_to_slice_view_len_and_index(ar: [u8; 3]) {
    trust_vc::assert!(ar.view().len() == 3usize);
    trust_vc::assert!(ar.view().index(1usize) == 5u8);
}

#[trust_vc::ensures(true)]
fn array_to_slice_ref_view_len_exact(ar: &[u8; 3]) {
    trust_vc::assert!(ar.view().len() == 3usize);
}

#[trust_vc::ensures(true)]
fn array_to_slice_ref_coercion_view_len_exact(ar: &[u8; 3]) {
    let sl: &[u8] = ar;
    trust_vc::assert!(sl.view().len() == 3usize);
}

#[trust_vc::ensures(true)]
fn array_to_slice_literal_view_len_and_index_exact() {
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().len() == 3usize);
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().index(1usize) == 5u8);
}

#[trust_vc::ensures(true)]
fn array_to_slice_local_ref_coercion_view_len_and_index_exact() {
    let ar = [4u8, 5u8, 6u8];
    let sl: &[u8] = &ar;
    trust_vc::assert!(sl.view().len() == 3usize);
    trust_vc::assert!(sl.view().index(1usize) == 5u8);
}

#[trust_vc::ensures(true)]
fn array_to_slice_literal_view_contains_exact() {
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().contains(4u8));
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().contains(6u8));
    trust_vc::assert!(!(&[4u8, 5u8, 6u8]).view().contains(7u8));
}

#[trust_vc::ensures(true)]
fn array_to_slice_literal_view_false_tail_counterexample() {
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().len() == 3usize);
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().index(1usize) == 5u8);
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().contains(6u8));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn array_to_slice_literal_view_wrong_contains_counterexample() {
    trust_vc::assert!((&[4u8, 5u8, 6u8]).view().contains(7u8));
}

#[trust_vc::ensures(true)]
fn array_to_slice_wrong_len_counterexample(ar: &[u8; 3]) {
    trust_vc::assert!(ar.view().len() == 4usize);
}

#[trust_vc::ensures(true)]
fn array_const_generic_view_len_currently_blocked<const N: usize>(ar: [u8; N]) {
    trust_vc::assert!(ar.view().len() == N);
}

#[trust_vc::requires(ar[1usize] == 4u8)]
#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_old_state_currently_blocked(ar: &mut [u8; 3]) {
    ar[1usize] += 1u8;
    trust_vc::assert!(ar[1usize] == old(ar)[1usize] + 1u8);
}

#[trust_vc::ensures(true)]
fn array_index_add_assign_mut_ref_alias_currently_blocked(ar: &mut [u8; 3]) {
    let alias: &mut [u8; 3] = ar;
    alias[1usize] += 1u8;
    trust_vc::assert!(alias[1usize] == 1u8);
}

fn array_index_side_effect_index(i: &mut usize) -> usize {
    *i += 1usize;
    0usize
}

#[trust_vc::ensures(true)]
fn array_index_add_assign_side_effect_index_currently_blocked(ar: &mut [usize; 20]) {
    let mut i = 0usize;
    ar[array_index_side_effect_index(&mut i)] += 1usize;
    trust_vc::assert!(ar[0usize] == 1usize);
}

#[trust_vc::ensures(true)]
fn array_literal_inequality() {
    trust_vc::assert!([10u8, 20u8, 30u8] != [10u8, 20u8, 40u8]);
    trust_vc::assert!([10u8, 20u8, 30u8].view() != [10u8, 20u8, 40u8].view());
}

#[trust_vc::ensures(true)]
fn array_named_inequality_and_contains() {
    let a1: [u8; 3] = [10u8, 20u8, 30u8];
    let a2: [u8; 3] = [10u8, 20u8, 40u8];
    trust_vc::assert!(a1 != a2);
    trust_vc::assert!(a1.view() != a2.view());
    trust_vc::assert!(a1.view().contains(30u8));
    trust_vc::assert!(!a2.view().contains(30u8));
}

#[trust_vc::ensures(true)]
fn array_literal_view_to_seq_index() {
    trust_vc::assert!(([10u8, 20u8, 30u8].view() as Seq<u8>).len() == 3usize);
    trust_vc::assert!(([10u8, 20u8, 30u8].view() as Seq<u8>).index(2usize) == 30u8);
}

#[trust_vc::ensures(true)]
fn array_literal_view_to_seq_inequality() {
    let s1: Seq<u8> = [10u8, 20u8, 30u8].view();
    let s2: Seq<u8> = [10u8, 20u8, 40u8].view();
    trust_vc::assert!(s1 != s2);
}

#[trust_vc::ensures(true)]
fn array_literal_view_to_seq_contains() {
    trust_vc::assert!(([10u8, 20u8, 30u8].view() as Seq<u8>).contains(30u8));
    trust_vc::assert!(!([10u8, 20u8, 30u8].view() as Seq<u8>).contains(40u8));
}

#[trust_vc::ensures(true)]
fn array_literal_view_seq_binding_contains() {
    let s: Seq<u8> = [10u8, 20u8, 30u8].view();
    trust_vc::assert!(s.contains(30u8));
}

#[trust_vc::ensures(true)]
fn array_literal_view_seq_binding_wrong_contains_counterexample() {
    let s: Seq<u8> = [10u8, 20u8, 30u8].view();
    trust_vc::assert!(s.contains(40u8));
}

#[trust_vc::ensures(true)]
fn array_literal_view_seq_binding_reuse() {
    let s: Seq<u8> = [10u8, 20u8, 30u8].view();
    trust_vc::assert!(s.contains(30u8));
    trust_vc::assert!(!s.contains(40u8));
}

#[trust_vc::ensures(true)]
fn array_literal_view_seq_binding_false_tail_counterexample() {
    let s: Seq<u8> = [10u8, 20u8, 30u8].view();
    trust_vc::assert!(s.contains(30u8));
    trust_vc::assert!(!s.contains(40u8));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn array_literal_view_contains() {
    trust_vc::assert!([10u8, 20u8, 30u8].view().contains(20u8));
    trust_vc::assert!(![10u8, 20u8, 30u8].view().contains(40u8));
}

#[trust_vc::ensures(true)]
fn array_named_view_contains() {
    trust_vc::assert!([10u8, 20u8, 30u8].view().contains(30u8));
    trust_vc::assert!(![10u8, 20u8, 40u8].view().contains(30u8));
}

#[trust_vc::ensures(true)]
fn array_named_view_contains_false_tail_counterexample() {
    trust_vc::assert!([10u8, 20u8, 30u8].view().contains(30u8));
    trust_vc::assert!(![10u8, 20u8, 40u8].view().contains(30u8));
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn array_named_view_wrong_contains_counterexample() {
    trust_vc::assert!([10u8, 20u8, 40u8].view().contains(30u8));
}

#[trust_vc::ensures(true)]
fn array_literal_six_wrong_first_counterexample() {
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().len() == 6usize);
    trust_vc::assert!([11u8, 12u8, 13u8, 14u8, 15u8, 16u8].view().index(0usize) == 12u8);
}

#[trust_vc::ensures(true)]
fn array_repeat_wrong_len_counterexample() {
    trust_vc::assert!([11u8; 6].view().len() == 7usize);
}

#[trust_vc::ensures(true)]
fn array_index_out_of_bounds(ar: [u8; 20]) {
    trust_vc::assert!(ar[20usize] == 0u8);
}

#[trust_vc::ensures(true)]
fn array_view_wrong_fixed_len(ar: [u8; 20]) {
    trust_vc::assert!(ar.view().len() == 21usize);
}
