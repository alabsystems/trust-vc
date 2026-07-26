// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Expanded partial executable TrustVc scout for upstream `overflow.rs`.
//!
//! The manifest entry remains `unsupported-gap`. This file intentionally ports
//! only Rust-valid, directly executable overflow-adjacent slices:
//! - bounded and unbounded finite integer addition/subtraction;
//! - guarded and unguarded division/remainder;
//! - in-range const arithmetic;
//! - primitive integer Add::add lowering;
//! - primitive shift width boundaries.
//!
//! Full upstream parity remains unsupported. The all-constant const/static
//! initializer overflow cases (`test_const_fail`, `test_static_fail`) are now
//! reproduced faithfully as constant-folded counterexamples (#2778). Verus-only
//! ghost/proof arithmetic, vstd `add`, the rustc literal-range diagnostic
//! (`test_literal_out_of_range`, a compile-time error on `256u8` that a
//! Rust-valid port cannot host), architecture-specific `usize` global-size
//! options, oversized-RHS and signed-negative spec bitshifts that currently
//! return solver `Unknown`, signed/negative shift diagnostics, non-primitive
//! vstd add/helper semantics, and broader nonlinear integer reasoning are only
//! recorded as gaps or fail-closed boundaries here, not replacement evidence.

#![allow(dead_code)]

use core::ops::Add;

pub type OverflowExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type OverflowFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const OVERFLOW_RS_EXPECTED_CASES: &[OverflowExpectedCase] = &[
    (
        "overflow_u64_add_by_two_guard_verified",
        "test_overflow_fails_1",
        "verified",
        2,
    ),
    (
        "overflow_u64_two_adds_guard_verified",
        "test_overflow_spec_fails_2",
        "verified",
        2,
    ),
    (
        "overflow_ensures_pass_usize_guard_verified",
        "test_overflow_ensures_pass",
        "verified",
        2,
    ),
    (
        "divide_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        "verified",
        2,
    ),
    (
        "remainder_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        "verified",
        1,
    ),
    (
        "const_u8_add_in_range_verified",
        "test_const_ok",
        "verified",
        1,
    ),
    (
        "underflow_u64_sub_guard_verified",
        "underflow",
        "verified",
        2,
    ),
    (
        "bit_shift_in_range_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_left_in_range_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_left_usize_bits_minus_one_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "nonlinear_unsigned_div_rem_guard_verified",
        "nonlinear_ops_dont_overflow_unsigned",
        "verified",
        2,
    ),
    (
        "arith_bounds_add_guard_verified",
        "arith_bounds_asserted_and_assumed",
        "verified",
        2,
    ),
    (
        "overflow_fails_u64_add_by_two_counterexample",
        "test_overflow_fails_1",
        "counterexample",
        1,
    ),
    (
        "overflow_two_u64_adds_second_counterexample",
        "test_overflow_fails_2",
        "counterexample",
        1,
    ),
    (
        "overflow_fails_usize_unbounded_counterexample",
        "test_overflow_fails_usize",
        "counterexample",
        1,
    ),
    (
        "divide_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        "counterexample",
        1,
    ),
    (
        "remainder_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        "counterexample",
        1,
    ),
    (
        "underflow_u64_sub_counterexample",
        "underflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_left_width_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_usize_bits_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "arith_bounds_add_missing_guard_counterexample",
        "arith_bounds_asserted_and_assumed",
        "counterexample",
        1,
    ),
    (
        "primitive_add_trait_method_verified",
        "test_overflow_spec_pass",
        "verified",
        2,
    ),
    (
        "const_item_initializer_overflow_counterexample",
        "test_const_fail",
        "counterexample",
        1,
    ),
    (
        "static_item_initializer_overflow_counterexample",
        "test_static_fail",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_mismatch_u32_counterexample",
        "bit_shift_width_mismatch",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_mismatch_signed_counterexample",
        "bit_shift_width_mismatch_signed",
        "counterexample",
        1,
    ),
    (
        "bit_shift_right_nonzero_left_arg_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_width_above_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_underflow_signed_fail_closed",
        "bit_shift_underflow",
        "error",
        1,
    ),
    (
        "bit_shift_unsigned_lhs_signed_shift_fail_closed",
        "bit_shift_unsigned_shift_signed",
        "error",
        1,
    ),
];

pub const OVERFLOW_RS_FAIL_CLOSED_ERROR_PATTERNS: &[OverflowFailClosedErrorPatterns] = &[
    (
        "bit_shift_underflow_signed_fail_closed",
        &["possible bit shift underflow/overflow"],
    ),
    (
        "bit_shift_unsigned_lhs_signed_shift_fail_closed",
        &["possible bit shift underflow/overflow"],
    ),
];

pub fn overflow_rs_expected_cases() -> &'static [OverflowExpectedCase] {
    OVERFLOW_RS_EXPECTED_CASES
}

pub fn overflow_rs_fail_closed_error_patterns() -> &'static [OverflowFailClosedErrorPatterns] {
    OVERFLOW_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn overflow_u64_add_by_two_guard_verified(a: u64) {
    trust_vc::assume!(a < 30u64);

    let b = a + 2u64;
    trust_vc::assert!(b == a + 2u64);
    trust_vc::assert!(b > a);
}

#[trust_vc::ensures(true)]
fn overflow_u64_two_adds_guard_verified(a: u64) {
    trust_vc::assume!(a < 30u64);

    let mut j = a;
    j = j + 2u64;
    trust_vc::assert!(j == a + 2u64);
    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

#[trust_vc::ensures(true)]
fn overflow_ensures_pass_usize_guard_verified(a: usize) {
    trust_vc::assume!(a < 30usize);

    let b = a + 1usize;
    trust_vc::assert!(b == a + 1usize);
    trust_vc::assert!(b > a);
}

#[trust_vc::ensures(true)]
fn overflow_fails_u64_add_by_two_counterexample(a: u64) {
    let b = a + 2u64;
    trust_vc::assert!(b > a);
}

#[trust_vc::ensures(true)]
fn overflow_two_u64_adds_second_counterexample(a: u64) {
    trust_vc::assume!(a >= 18446744073709551613u64);

    let mut j = a;
    j = j + 2u64;
    j = j + 2u64;
    trust_vc::assert!(j > a);
}

#[trust_vc::ensures(true)]
fn overflow_fails_usize_unbounded_counterexample(a: usize) {
    let b = a + 1usize;
    trust_vc::assert!(b > a);
}

#[trust_vc::ensures(true)]
fn divide_by_nonzero_u8_guard_verified(a: u8, b: u8) {
    trust_vc::assume!(b != 0u8);

    trust_vc::assert!(a / b == a / b);
    trust_vc::assert!(a % b == a % b);
}

#[trust_vc::ensures(true)]
fn remainder_by_nonzero_u8_guard_verified(a: u8, b: u8) {
    trust_vc::assume!(b != 0u8);

    trust_vc::assert!(a % b == a % b);
}

#[trust_vc::ensures(true)]
fn divide_by_zero_guard_missing_counterexample(a: u8, b: u8) {
    let q = a / b;
    trust_vc::assert!(b != 0u8 && q == q);
}

#[trust_vc::ensures(true)]
fn remainder_by_zero_guard_missing_counterexample(a: u8, b: u8) {
    let r = a % b;
    trust_vc::assert!(b != 0u8 && r == r);
}

#[trust_vc::ensures(true)]
fn const_u8_add_in_range_verified() {
    let c: u8 = 254u8 + 1u8;
    trust_vc::assert!(c == 255u8);
}

#[trust_vc::ensures(true)]
fn underflow_u64_sub_guard_verified(a: u64) {
    trust_vc::assume!(a > 0u64);

    let b = a - 1u64;
    trust_vc::assert!(b == a - 1u64);
    trust_vc::assert!(b < a);
}

#[trust_vc::ensures(true)]
fn underflow_u64_sub_counterexample(a: u64) {
    trust_vc::assume!(a == 0u64);

    let b = a - 1u64;
    trust_vc::assert!(b < a);
}

#[trust_vc::ensures(true)]
fn bit_shift_in_range_u16_verified(x: u16) {
    let y: u16 = 15u16;
    trust_vc::assert!(x >> y == x >> y);
}

#[trust_vc::ensures(true)]
fn bit_shift_right_nonzero_left_arg_u16_verified() {
    let x: u16 = 16u16;
    let y: u16 = 5u16;
    trust_vc::assert!(x >> y == 0u16);
}

#[trust_vc::ensures(true)]
fn bit_shift_left_in_range_u16_verified(x: u16) {
    let y: u16 = 15u16;
    trust_vc::assert!(x << y == x << y);
}

#[trust_vc::ensures(true)]
fn bit_shift_left_usize_bits_minus_one_verified(x: usize) {
    let y: usize = (usize::BITS - 1u32) as usize;
    trust_vc::assert!(x << y == x << y);
}

#[trust_vc::ensures(true)]
fn nonlinear_unsigned_div_rem_guard_verified(a: u32, b: u32) {
    trust_vc::assume!(b != 0u32);

    let x = a / b;
    let y = a % b;
    trust_vc::assert!(x == a / b);
    trust_vc::assert!(y == a % b);
}

#[trust_vc::ensures(true)]
fn arith_bounds_add_guard_verified(a: u64, b: u64) {
    trust_vc::assume!(a < 30u64);
    trust_vc::assume!(b < 30u64);

    let z = a + b;
    let y = a + b;
    trust_vc::assert!(z == a + b);
    trust_vc::assert!(z == y);
}

#[trust_vc::ensures(true)]
fn bit_shift_width_boundary_counterexample(x: u16) {
    let y: u16 = 16u16;
    trust_vc::assert!(x >> y == x >> y);
}

#[trust_vc::ensures(true)]
fn bit_shift_width_above_boundary_counterexample(x: u16) {
    let y: u16 = 17u16;
    trust_vc::assert!(x >> y == x >> y);
}

#[trust_vc::ensures(true)]
fn bit_shift_left_width_boundary_counterexample(x: u16) {
    let y: u16 = 16u16;
    trust_vc::assert!(x << y == x << y);
}

#[trust_vc::ensures(true)]
fn bit_shift_usize_bits_boundary_counterexample(x: usize) {
    let y: usize = usize::BITS as usize;
    trust_vc::assert!(x << y == x << y);
}

#[trust_vc::ensures(true)]
fn arith_bounds_add_missing_guard_counterexample(a: u64, b: u64) {
    let z = a + b;
    trust_vc::assert!(z >= a);
}

#[trust_vc::ensures(true)]
fn primitive_add_trait_method_verified() {
    let a: usize = 2usize;
    let b: usize = 3usize;
    let c1 = a + b;
    let c2 = a.add(b);

    trust_vc::assert!(c1 == 5usize);
    trust_vc::assert!(c1 == c2);
}

#[trust_vc::ensures(true)]
fn const_item_initializer_overflow_counterexample() {
    // Upstream test_const_fail: `const C: u8 = 255 + 1 /* FAILS */`.
    // The all-constant initializer overflows u8, so the exec-mode arithmetic
    // overflow obligation is refuted (constant-folded counterexample). #2778.
    const C: u8 = 255u8 + 1u8;

    trust_vc::assert!(C == 0u8);
}

#[trust_vc::ensures(true)]
fn static_item_initializer_overflow_counterexample() {
    // Upstream test_static_fail: `exec static C: u8 = 255 + 1 /* FAILS */`.
    // Same overflowing initializer as the const case; the static binding's
    // initializer carries the same exec-mode overflow obligation. #2778.
    static C: u8 = 255u8 + 1u8;

    trust_vc::assert!(C == 0u8);
}

#[trust_vc::ensures(true)]
fn bit_shift_width_mismatch_u32_counterexample(x: u16) {
    let y: u32 = 40u32;
    let z = x << y;

    trust_vc::assert!(z == z);
}

#[trust_vc::ensures(true)]
fn bit_shift_width_mismatch_signed_counterexample(x: u16) {
    let y: i32 = -1i32;
    let z = x << y;

    trust_vc::assert!(z == z);
}

fn bit_shift_underflow_signed_fail_closed(x: i16) {
    let y: i16 = -1i16;
    let z = x << y;

    trust_vc::assert!(z == z);
}

fn bit_shift_unsigned_lhs_signed_shift_fail_closed(x: u16) {
    let y: i16 = -1i16;
    let z = x << y;

    trust_vc::assert!(z == z);
}
