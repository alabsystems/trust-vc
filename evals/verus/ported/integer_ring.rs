// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! First partial executable TrustVc scout for upstream integer_ring.rs.
//!
//! This is intentionally not replacement evidence for Verus `by(integer_ring)`
//! or Singular integration. It covers only a small Rust-valid arithmetic slice:
//! bounded symbolic and concrete polynomial identities currently expressible
//! through TrustVc nonlinear arithmetic, upstream-shaped false polynomial
//! identities, concrete modular witnesses, and modular/arithmetic boundaries
//! that remain fail-closed instead of pretending to be Singular-backed
//! integer-ring proofs.

#![allow(dead_code)]

use trust_vc_types::int;

pub type IntegerRingRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type IntegerRingRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const INTEGER_RING_RS_EXPECTED_CASES: &[IntegerRingRsExpectedCase] = &[
    (
        "simple_2_bounded_factorization_verified",
        "simple_2",
        "verified",
        1,
    ),
    (
        "simple_2_trinomial_square_concrete_verified",
        "simple_2",
        "verified",
        1,
    ),
    (
        "simple_2_bounded_double_offset_factorization_verified",
        "simple_2",
        "verified",
        1,
    ),
    (
        "mul_mod_noop_concrete_verified",
        "mul_mod_noop",
        "verified",
        3,
    ),
    (
        "reserved_keyword_name_polynomial_shape_verified",
        "reserved_keyword",
        "verified",
        1,
    ),
    (
        "wide_mul_limb_expansion_concrete_verified",
        "wide_mul",
        "verified",
        1,
    ),
    (
        "simple_2_bounded_factorization_wrong_increment_counterexample",
        "simple_fail_2",
        "counterexample",
        1,
    ),
    (
        "simple_2_bounded_double_offset_wrong_factor_counterexample",
        "simple_fail_2",
        "counterexample",
        1,
    ),
    (
        "simple_fail_2_trinomial_missing_square_concrete_counterexample",
        "simple_fail_2",
        "counterexample",
        1,
    ),
    (
        "simple_fail_1_modular_addition_concrete_counterexample",
        "simple_fail_1",
        "counterexample",
        2,
    ),
    (
        "mul_mod_noop_fail_1_concrete_counterexample",
        "mul_mod_noop_fail_1",
        "counterexample",
        2,
    ),
    (
        "mul_mod_noop_fail_2_concrete_counterexample",
        "mul_mod_noop_fail_2",
        "counterexample",
        2,
    ),
    (
        "wide_mul_wrong_limb_concrete_counterexample",
        "wide_mul_fail",
        "counterexample",
        1,
    ),
    (
        "simple_1_modular_multiplication_singular_boundary",
        "simple_1",
        "error",
        0,
    ),
    (
        "mont_mul_1_singular_boundary",
        "mont_mul_1",
        "error",
        0,
    ),
    (
        "mont_mul_2_singular_boundary",
        "mont_mul_2",
        "error",
        0,
    ),
    (
        "mul_mod_noop_singular_boundary",
        "mul_mod_noop",
        "error",
        0,
    ),
    (
        "uninterpreted_function_singular_boundary",
        "uninterpreted_function",
        "error",
        0,
    ),
    (
        "type_fail_mixed_u32_singular_boundary",
        "type_fail",
        "error",
        0,
    ),
    ("warnings_singular_boundary", "warnings", "error", 0),
    (
        "gt_not_supported_singular_boundary",
        "gt_not_supported",
        "error",
        0,
    ),
    (
        "lt_not_supported_singular_boundary",
        "lt_not_supported",
        "error",
        0,
    ),
    (
        "div_by_zero_singular_boundary",
        "div_by_zero_fail",
        "error",
        0,
    ),
    (
        "simple_1_modular_multiplication_concrete_verified",
        "simple_1",
        "verified",
        2,
    ),
    (
        "mont_mul_1_concrete_verified",
        "mont_mul_1",
        "verified",
        4,
    ),
    (
        "mont_mul_2_concrete_verified",
        "mont_mul_2",
        "verified",
        5,
    ),
    (
        "uninterpreted_function_concrete_verified",
        "uninterpreted_function",
        "verified",
        2,
    ),
    (
        "type_fail_mixed_u32_modular_concrete_verified",
        "type_fail",
        "verified",
        2,
    ),
    (
        "warnings_modular_concrete_verified",
        "warnings",
        "verified",
        6,
    ),
    (
        "gt_not_supported_concrete_counterexample",
        "gt_not_supported",
        "counterexample",
        2,
    ),
    (
        "lt_not_supported_concrete_counterexample",
        "lt_not_supported",
        "counterexample",
        2,
    ),
];

pub fn integer_ring_rs_expected_cases() -> &'static [IntegerRingRsExpectedCase] {
    INTEGER_RING_RS_EXPECTED_CASES
}

pub const INTEGER_RING_RS_EXPECTED_ERROR_PATTERNS: &[IntegerRingRsExpectedErrorPatterns] = &[
    (
        "simple_1_modular_multiplication_singular_boundary",
        &[
            "unknown return type for function 'simple_1_modular_congruence'",
            "simple_1_modular_congruence",
        ],
    ),
    (
        "mont_mul_1_singular_boundary",
        &[
            "unknown return type for function 'mont_mul_1_modular_congruence'",
            "mont_mul_1_modular_congruence",
        ],
    ),
    (
        "mont_mul_2_singular_boundary",
        &[
            "unknown return type for function 'mont_mul_2_modular_zero'",
            "mont_mul_2_modular_zero",
        ],
    ),
    (
        "mul_mod_noop_singular_boundary",
        &[
            "unknown return type for function 'mul_mod_noop_identity'",
            "mul_mod_noop_identity",
        ],
    ),
    (
        "uninterpreted_function_singular_boundary",
        &[
            "unknown return type for function 'uninterpreted_function_modular_relation'",
            "uninterpreted_function_modular_relation",
        ],
    ),
    (
        "type_fail_mixed_u32_singular_boundary",
        &[
            "unknown return type for function 'type_fail_mixed_u32_modular_relation'",
            "type_fail_mixed_u32_modular_relation",
        ],
    ),
    (
        "warnings_singular_boundary",
        &[
            "unknown return type for function 'warnings_modular_relation'",
            "warnings_modular_relation",
        ],
    ),
    (
        "gt_not_supported_singular_boundary",
        &[
            "unknown return type for function 'integer_ring_gt_relation'",
            "integer_ring_gt_relation",
        ],
    ),
    (
        "lt_not_supported_singular_boundary",
        &[
            "unknown return type for function 'integer_ring_lt_relation'",
            "integer_ring_lt_relation",
        ],
    ),
    (
        "div_by_zero_singular_boundary",
        &[
            "unknown return type for function 'may_div_zero_relation'",
            "may_div_zero_relation",
        ],
    ),
];

pub fn integer_ring_rs_expected_error_patterns() -> &'static [IntegerRingRsExpectedErrorPatterns] {
    INTEGER_RING_RS_EXPECTED_ERROR_PATTERNS
}

fn simple_1_modular_congruence(x: int, y: int, m: int) -> bool {
    (x - y) % m == 0
}

fn mont_mul_1_modular_congruence(a: int, s: int, r: int, m: int, rr: int, r_inv: int) -> bool {
    (a * r - rr * s) % m == 0 && (r_inv * r - 1) % m == 0 && rr - r * r % m == 0
}

fn mont_mul_2_modular_zero(
    p2_full: int,
    base: int,
    ui: int,
    m0: int,
    m0d: int,
    p1_lh: int,
    p1_full: int,
) -> bool {
    p2_full == ui * m0 + p1_lh
        && (p1_full - p1_lh) % base == 0
        && (m0d * m0 - (base - 1)) % base == 0
        && (ui - p1_full * m0d) % base == 0
}

fn mul_mod_noop_identity(x: int, y: int, m: int) -> bool {
    ((x % m) * y) % m == (x * y) % m
        && (x * (y % m)) % m == (x * y) % m
        && ((x % m) * (y % m)) % m == (x * y) % m
}

fn uninterpreted_function_modular_relation(x: int, y: int, m: int) -> bool {
    (x * x * x * x - y * y * y * y) % m == 0
}

fn type_fail_mixed_u32_modular_relation(x: u32, y: u32, z: u32, m: int) -> bool {
    ((x as int) * (z as int) - (y as int) * (z as int)) % m == 0
}

fn warnings_modular_relation(
    x: int,
    y: int,
    d: int,
    small_x: int,
    small_y: int,
    tmp1: int,
    tmp2: int,
) -> bool {
    small_x == x % d
        && small_y == y % d
        && tmp1 == (small_y - small_x) % d
        && tmp2 == (y - x) % d
        && (tmp1 - tmp2) % d == 0
}

fn integer_ring_gt_relation(x: int, y: int, z: int, m: int) -> bool {
    (x - y) % m > 0 && (x * z + y * z) % m == 0
}

fn integer_ring_lt_relation(x: int, y: int, z: int, m: int) -> bool {
    (x - y) % m == 0 && (x * z + y * z) % m < 0
}

fn may_div_zero_relation(x: int) -> bool {
    x % x == 0
}

#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn simple_2_bounded_factorization_verified(x: u32) {
    trust_vc::assert_by_nonlinear!(
        x * x + x == x * (x + 1u32);
        requires x < 0xfffu32
    );
}

#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn simple_2_bounded_factorization_wrong_increment_counterexample(x: u32) {
    trust_vc::assert_by_nonlinear!(
        x * x + x == x * (x + 2u32);
        requires x < 0xfffu32
    );
}

#[trust_vc::ensures(true)]
fn simple_2_trinomial_square_concrete_verified() {
    let x: u32 = 2;
    let y: u32 = 3;
    let z: u32 = 5;

    trust_vc::assert_by_nonlinear!(
        (x + y + z) * (x + y + z) == x * x + y * y + z * z + 2u32 * (x * y + y * z + z * x)
    );
}

#[trust_vc::requires(x <= 1000u32)]
#[trust_vc::ensures(true)]
fn simple_2_bounded_double_offset_factorization_verified(x: u32) {
    trust_vc::assert_by_nonlinear!(
        x * x + 2u32 * x == x * (x + 2u32);
        requires x <= 1000u32
    );
}

#[trust_vc::requires(x <= 1000u32)]
#[trust_vc::ensures(true)]
fn simple_2_bounded_double_offset_wrong_factor_counterexample(x: u32) {
    trust_vc::assert_by_nonlinear!(
        x * x + 2u32 * x == x * (x + 3u32);
        requires x <= 1000u32
    );
}

#[trust_vc::ensures(true)]
fn simple_fail_2_trinomial_missing_square_concrete_counterexample() {
    let x: u32 = 0;
    let y: u32 = 0;
    let z: u32 = 2;

    trust_vc::assert_by_nonlinear!(
        (x + y + z) * (x + y + z) == x * x + y * y + z + 2u32 * (x * y + y * z + z * x)
    );
}

#[trust_vc::ensures(true)]
fn simple_fail_1_modular_addition_concrete_counterexample() {
    let x: int = 1;
    let y: int = 1;
    let z: int = 1;
    let m: int = 3;

    trust_vc::assert!((x - y) % m == 0);
    trust_vc::assert!((x * z + y * z) % m == 0);
}

#[trust_vc::ensures(true)]
fn simple_1_modular_multiplication_concrete_verified() {
    let x: int = 7;
    let y: int = 2;
    let z: int = 3;
    let m: int = 5;

    trust_vc::assert!((x - y) % m == 0);
    trust_vc::assert!((x * z - y * z) % m == 0);
}

#[trust_vc::ensures(true)]
fn mont_mul_1_concrete_verified() {
    let a: int = 3;
    let s: int = 1;
    let r: int = 3;
    let m: int = 5;
    let rr: int = 4;
    let r_inv: int = 2;

    trust_vc::assert!((a * r - rr * s) % m == 0);
    trust_vc::assert!((r_inv * r - 1) % m == 0);
    trust_vc::assert!(rr - r * r % m == 0);
    trust_vc::assert!((a - s * r) % m == 0);
}

#[trust_vc::ensures(true)]
fn mont_mul_2_concrete_verified() {
    let p2_full: int = 20;
    let base: int = 10;
    let ui: int = 2;
    let m0: int = 7;
    let m0d: int = 7;
    let p1_lh: int = 6;
    let p1_full: int = 6;

    trust_vc::assert!(p2_full == ui * m0 + p1_lh);
    trust_vc::assert!((p1_full - p1_lh) % base == 0);
    trust_vc::assert!((m0d * m0 - (base - 1)) % base == 0);
    trust_vc::assert!((ui - p1_full * m0d) % base == 0);
    trust_vc::assert!(p2_full % base == 0);
}

#[trust_vc::ensures(true)]
fn mul_mod_noop_concrete_verified() {
    let x: int = 14;
    let y: int = 9;
    let m: int = 5;

    trust_vc::assert!(((x % m) * y) % m == (x * y) % m);
    trust_vc::assert!((x * (y % m)) % m == (x * y) % m);
    trust_vc::assert!(((x % m) * (y % m)) % m == (x * y) % m);
}

#[trust_vc::ensures(true)]
fn mul_mod_noop_fail_1_concrete_counterexample() {
    let x: int = 2;
    let y: int = 2;
    let m: int = 5;

    trust_vc::assert!(((x % m) * y) % m == (x * y) % m);
    trust_vc::assert!(((x % m) * (y % m)) % m == x % m);
}

#[trust_vc::ensures(true)]
fn mul_mod_noop_fail_2_concrete_counterexample() {
    let x: int = 2;
    let y: int = 2;
    let m: int = 5;

    trust_vc::assert!(((x % m) * y) % m == (x * y) % m);
    trust_vc::assert!(((x % m) * (y % m)) % m == x % m);
    trust_vc::assert!((x * (y % m)) % m == x % m);
}

#[trust_vc::ensures(true)]
fn uninterpreted_function_concrete_verified() {
    let x: int = 2;
    let y: int = 7;
    let m: int = 5;
    let square_x: int = x * x;
    let square_y: int = y * y;
    let quad_x: int = x * x * x * x;
    let quad_y: int = y * y * y * y;

    trust_vc::assert!((square_x - square_y) % m == 0);
    trust_vc::assert!((quad_x - quad_y) % m == 0);
}

#[trust_vc::ensures(true)]
fn type_fail_mixed_u32_modular_concrete_verified() {
    let x: u32 = 2;
    let y: u32 = 2;
    let z: u32 = 3;
    let m: int = 5;

    trust_vc::assert!(((x as int) - (y as int)) % m == 0);
    trust_vc::assert!(((x as int) * (z as int) - (y as int) * (z as int)) % m == 0);
}

#[trust_vc::ensures(true)]
fn reserved_keyword_name_polynomial_shape_verified() {
    let singular_tmp_1: int = 7;
    let y: int = 4;
    let z: int = 3;

    trust_vc::assert_by_nonlinear!(singular_tmp_1 * z - y * z == (singular_tmp_1 - y) * z);
}

#[trust_vc::ensures(true)]
fn wide_mul_limb_expansion_concrete_verified() {
    let b: int = 10;
    let x_0: int = 0;
    let x_1: int = 0;
    let x_2: int = 1;
    let x_3: int = 0;
    let y_0: int = 0;
    let y_1: int = 1;
    let y_2: int = 0;
    let y_3: int = 0;
    let x: int = x_0 + x_1 * b + x_2 * b * b + x_3 * b * b * b;
    let y: int = y_0 + y_1 * b + y_2 * b * b + y_3 * b * b * b;
    let p0: int = x_0 * y_0;
    let p1: int = x_1 * y_0;
    let p2: int = x_0 * y_1;
    let p3: int = x_2 * y_0;
    let p4: int = x_1 * y_1;
    let p5: int = x_0 * y_2;
    let p6: int = x_3 * y_0;
    let p7: int = x_2 * y_1;
    let p8: int = x_1 * y_2;
    let p9: int = x_0 * y_3;
    let p10: int = x_3 * y_1;
    let p11: int = x_2 * y_2;
    let p12: int = x_1 * y_3;
    let p13: int = x_3 * y_2;
    let p14: int = x_2 * y_3;
    let p15: int = x_3 * y_3;

    trust_vc::assert!(
        x * y
            == p0
                + (p1 + p2) * b
                + (p3 + p4 + p5) * b * b
                + (p6 + p7 + p8 + p9) * b * b * b
                + (p10 + p11 + p12) * b * b * b * b
                + (p13 + p14) * b * b * b * b * b
                + p15 * b * b * b * b * b * b
    );
}

#[trust_vc::ensures(true)]
fn wide_mul_wrong_limb_concrete_counterexample() {
    let b: int = 10;
    let x_0: int = 0;
    let x_1: int = 0;
    let x_2: int = 1;
    let x_3: int = 0;
    let y_0: int = 0;
    let y_1: int = 1;
    let y_2: int = 0;
    let y_3: int = 0;
    let x: int = x_0 + x_1 * b + x_2 * b * b + x_3 * b * b * b;
    let y: int = y_0 + y_1 * b + y_2 * b * b + y_3 * b * b * b;
    let p0: int = x_0 * y_0;
    let p1: int = x_1 * y_0;
    let p2: int = x_0 * y_1;
    let p3: int = x_2 * y_0;
    let p4: int = x_1 * y_1;
    let p5: int = x_0 * y_2;
    let p6: int = x_3 * y_0;
    let p7: int = x_2 * y_2;
    let p8: int = x_1 * y_2;
    let p9: int = x_0 * y_3;
    let p10: int = x_3 * y_1;
    let p11: int = x_2 * y_2;
    let p12: int = x_1 * y_3;
    let p13: int = x_3 * y_2;
    let p14: int = x_2 * y_3;
    let p15: int = x_3 * y_3;

    trust_vc::assert!(
        x * y
            == p0
                + (p1 + p2) * b
                + (p3 + p4 + p5) * b * b
                + (p6 + p7 + p8 + p9) * b * b * b
                + (p10 + p11 + p12) * b * b * b * b
                + (p13 + p14) * b * b * b * b * b
                + p15 * b * b * b * b * b * b
    );
}

#[trust_vc::ensures(true)]
fn gt_not_supported_concrete_counterexample() {
    let x: int = 2;
    let y: int = 1;
    let z: int = 1;
    let m: int = 5;

    trust_vc::assert!((x - y) % m > 0);
    trust_vc::assert!((x * z + y * z) % m == 0);
}

#[trust_vc::ensures(true)]
fn lt_not_supported_concrete_counterexample() {
    let x: int = 1;
    let y: int = 1;
    let z: int = 1;
    let m: int = 5;

    trust_vc::assert!((x - y) % m == 0);
    trust_vc::assert!((x * z + y * z) % m < 0);
}

#[trust_vc::ensures(true)]
fn warnings_modular_concrete_verified() {
    let x: int = 8;
    let y: int = 14;
    let d: int = 5;
    let small_x: int = 3;
    let small_y: int = 4;
    let tmp1: int = 1;
    let tmp2: int = 1;

    trust_vc::assert!(d + 1 != 0);
    trust_vc::assert!(small_x == x % d);
    trust_vc::assert!(small_y == y % d);
    trust_vc::assert!(tmp1 == (small_y - small_x) % d);
    trust_vc::assert!(tmp2 == (y - x) % d);
    trust_vc::assert!((tmp1 - tmp2) % d == 0);
}

#[trust_vc::requires(m != 0)]
#[trust_vc::requires((x - y) % m == 0)]
#[trust_vc::ensures(true)]
fn simple_1_modular_multiplication_singular_boundary(x: int, y: int, z: int, m: int) {
    trust_vc::assert!(simple_1_modular_congruence(x * z, y * z, m));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::requires((a * r - rr * s) % m == 0)]
#[trust_vc::requires((r_inv * r - 1) % m == 0)]
#[trust_vc::requires(rr - r * r % m == 0)]
#[trust_vc::ensures(true)]
fn mont_mul_1_singular_boundary(a: int, s: int, r: int, m: int, rr: int, r_inv: int) {
    trust_vc::assert!(mont_mul_1_modular_congruence(a, s, r, m, rr, r_inv));
}

#[trust_vc::requires(base != 0)]
#[trust_vc::requires(p2_full == ui * m0 + p1_lh)]
#[trust_vc::requires((p1_full - p1_lh) % base == 0)]
#[trust_vc::requires((m0d * m0 - (base - 1)) % base == 0)]
#[trust_vc::requires((ui - p1_full * m0d) % base == 0)]
#[trust_vc::ensures(true)]
fn mont_mul_2_singular_boundary(
    p2_full: int,
    base: int,
    ui: int,
    m0: int,
    m0d: int,
    p1_lh: int,
    p1_full: int,
) {
    trust_vc::assert!(mont_mul_2_modular_zero(
        p2_full, base, ui, m0, m0d, p1_lh, p1_full
    ));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::requires((x * x - y * y) % m == 0)]
#[trust_vc::ensures(true)]
fn uninterpreted_function_singular_boundary(x: int, y: int, m: int) {
    trust_vc::assert!(uninterpreted_function_modular_relation(x, y, m));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::ensures(true)]
fn type_fail_mixed_u32_singular_boundary(x: u32, y: u32, z: u32, m: int) {
    trust_vc::assert!(type_fail_mixed_u32_modular_relation(x, y, z, m));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::ensures(true)]
fn mul_mod_noop_singular_boundary(x: int, y: int, m: int) {
    trust_vc::assert!(mul_mod_noop_identity(x, y, m));
}

#[trust_vc::requires(d + 1 != 0)]
#[trust_vc::ensures(true)]
fn warnings_singular_boundary(
    x: int,
    y: int,
    d: int,
    small_x: int,
    small_y: int,
    tmp1: int,
    tmp2: int,
) {
    trust_vc::assert!(warnings_modular_relation(
        x, y, d, small_x, small_y, tmp1, tmp2
    ));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::requires((x - y) % m > 0)]
#[trust_vc::ensures(true)]
fn gt_not_supported_singular_boundary(x: int, y: int, z: int, m: int) {
    trust_vc::assert!(integer_ring_gt_relation(x, y, z, m));
}

#[trust_vc::requires(m != 0)]
#[trust_vc::requires((x - y) % m == 0)]
#[trust_vc::ensures(true)]
fn lt_not_supported_singular_boundary(x: int, y: int, z: int, m: int) {
    trust_vc::assert!(integer_ring_lt_relation(x, y, z, m));
}

#[trust_vc::ensures(true)]
fn div_by_zero_singular_boundary(x: int) {
    trust_vc::assert!(may_div_zero_relation(x));
}
