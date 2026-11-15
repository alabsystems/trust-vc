// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused partial executable TrustVc port for upstream integers.rs.
//!
//! This file intentionally covers only Rust-valid slices of the pinned
//! upstream numeric surface: int/nat arithmetic, finite-integer casts into and
//! out of mathematical integers and nat, boundary literals, bool-to-int casts,
//! chained integer comparisons/equalities, fieldless enum casts, and
//! upstream-shaped arithmetic counterexamples. Verus-only int/nat syntax,
//! Integer trait sealing, Step specs, enum-cast diagnostics, and full diagnostic
//! parity remain unsupported here.

#![allow(dead_code)]

use trust_vc_types::{int, nat};

pub const INTEGERS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1_int_nat_arithmetic", "test1", "verified", 17),
    (
        "test1_fails_wrapping_add_counterexample",
        "test1_fails",
        "counterexample",
        2,
    ),
    (
        "test1_symbolic_division_remainder_verified",
        "test1",
        "verified",
        4,
    ),
    (
        "test2_fails_u8_wrapped_256_counterexample",
        "test2_fails",
        "counterexample",
        2,
    ),
    (
        "test3_fails_signed_division_counterexample",
        "test3_fails",
        "counterexample",
        2,
    ),
    (
        "test_chained_nat_bounds_verified",
        "test_chained",
        "verified",
        4,
    ),
    (
        "test_chained_nat_bounds_counterexample",
        "test_chained",
        "counterexample",
        2,
    ),
    (
        "test_chained_equalities_verified",
        "test_chained1",
        "verified",
        7,
    ),
    (
        "test_chained_equalities_counterexample",
        "test_chained1",
        "counterexample",
        2,
    ),
    ("test4_explicit_cast_typing_surface", "test4", "verified", 8),
    ("test_literals_boundaries", "test_literals", "verified", 7),
    (
        "test_literals_fails_wrong_zero_boundary_counterexample",
        "test_literals_fails1",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_u8_boundary_counterexample",
        "test_literals_fails2",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_i8_low_boundary_counterexample",
        "test_literals_fails3",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_i8_high_boundary_counterexample",
        "test_literals_fails4",
        "counterexample",
        2,
    ),
    (
        "test_spec_const_like_large_arithmetic",
        "test_spec_const",
        "verified",
        4,
    ),
    ("test_bool_to_int", "test_bool_to_int", "verified", 5),
    (
        "test_enum_to_int_discriminant_constants",
        "test_enum_to_int",
        "verified",
        4,
    ),
    (
        "test_enum_to_int_discriminant_liar_counterexample",
        "test_enum_to_int",
        "counterexample",
        2,
    ),
    (
        "test_enum_to_int_symbolic_return",
        "test_enum_to_int",
        "verified",
        3,
    ),
    (
        "test_enum_to_int_symbolic_return_liar_counterexample",
        "test_enum_to_int",
        "counterexample",
        2,
    ),
    ("test_finite_unsigned_to_nat_casts", "test1", "verified", 6),
    (
        "test_nat_to_finite_cast_wrap_constant",
        "test4",
        "verified",
        3,
    ),
    (
        "test_finite_signed_to_nat_cast_nonnegative",
        "finite_signed_to_nat_nonnegative",
        "verified",
        3,
    ),
];

pub fn integers_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    INTEGERS_RS_EXPECTED_CASES
}

#[trust_vc::spec]
fn add1_int(i: int) -> int {
    i + 1
}

#[trust_vc::spec]
fn add1_int_left(i: int) -> int {
    1 + i
}

#[trust_vc::spec]
fn add1_nat(i: nat) -> nat {
    i + 1
}

#[trust_vc::spec]
fn add1_nat_left(i: nat) -> nat {
    1 + i
}

#[trust_vc::spec]
fn add_nat_nat(i: nat, j: nat) -> nat {
    i + j
}

#[trust_vc::spec]
fn add_nat_u8(i: nat, j: u8) -> int {
    (i as int) + (j as int)
}

#[trust_vc::spec]
fn add_u8_nat(i: u8, j: nat) -> int {
    (i as int) + (j as int)
}

#[trust_vc::spec]
fn nat_one_hundred() -> nat {
    100
}

#[derive(Copy, Clone)]
enum IntegerCastEnum {
    A,
    B = 255,
    C,
}

#[trust_vc::ensures(true)]
fn test1_int_nat_arithmetic(n: nat, u: u8) {
    trust_vc::assert!(n >= 0);
    trust_vc::assert!(u >= 0);
    trust_vc::assert!(n + n >= 0);
    trust_vc::assert!(add_nat_nat(n, n) == n + n);
    trust_vc::assert!((u as int) >= 0);
    trust_vc::assert!((u as int) < 256);
    trust_vc::assert!((u as int) + (u as int) < 512);
    trust_vc::assert!(!(u < 100) || (u as int) + (u as int) < 250);
    trust_vc::assert!(add1_int(u as int) == (u as int) + 1);
    trust_vc::assert!(add1_int_left(u as int) == (u as int) + 1);
    trust_vc::assert!(add1_nat(n) == n + 1);
    trust_vc::assert!(add1_nat(u as nat) == (u as nat) + 1);
    trust_vc::assert!(add1_nat_left(n) == n + 1);
    trust_vc::assert!(add_nat_u8(n, u) == (n as int) + (u as int));
    trust_vc::assert!(add_u8_nat(u, n) == (u as int) + (n as int));
    trust_vc::assert!(nat_one_hundred() >= 0);
}

#[trust_vc::ensures(true)]
fn test1_fails_wrapping_add_counterexample(u: u8) {
    trust_vc::assert!(add1_int(u as int) == (u.wrapping_add(1) as int));
}

#[trust_vc::ensures(true)]
fn test1_symbolic_division_remainder_verified(n: nat, u: u8) {
    trust_vc::assert!(n / 2 <= n);
    trust_vc::assert!(u / 2 <= u);
    trust_vc::assert!(u % 10 < 10);
}

#[trust_vc::ensures(true)]
fn test2_fails_u8_wrapped_256_counterexample(u: u8) {
    let wrapped: u8 = 0;
    trust_vc::assert!(u < wrapped);
}

#[trust_vc::ensures(true)]
fn test3_fails_signed_division_counterexample(i: int, n: nat) {
    trust_vc::assert!(i / 2 <= n);
}

#[trust_vc::ensures(true)]
fn test_chained_nat_bounds_verified(n: nat) {
    trust_vc::assert!(0 <= n);
    trust_vc::assert!((n as int) < (n as int) + 1);
    trust_vc::assert!((n as int) + 1 < (n as int) + 2);
}

#[trust_vc::ensures(true)]
fn test_chained_nat_bounds_counterexample(n: nat) {
    trust_vc::assert!((n as int) + 1 < n);
}

#[trust_vc::ensures(true)]
fn test_chained_equalities_verified(n: nat) {
    let ni: int = n as int;

    trust_vc::assert!(ni == ni + 0);
    trust_vc::assert!(ni == 0 + ni);
    trust_vc::assert!(2 == 1 + 1);
    trust_vc::assert!(2 == 3 - 1);
    trust_vc::assert!(ni == ni * 1);
    trust_vc::assert!(ni == 1 * ni);
}

#[trust_vc::ensures(true)]
fn test_chained_equalities_counterexample(n: nat) {
    trust_vc::assert!(1 + (n as int) == 1);
}

#[trust_vc::ensures(true)]
fn test4_explicit_cast_typing_surface(u: u64, i: int, n: nat) {
    let _u2: u64 = i as u64;
    let i2: int = u as int;
    let i3: int = u as int;
    let i5: int = n as int;
    let n3: nat = 10;
    let i6: int = -10;
    let x: int = 2 + 2;
    let _b1: bool = (u as int) <= i;
    let _b2: bool = i <= (u as int);
    let _b3: bool = (u as int) <= i + 1;
    let _b4: bool = i + 1 <= (u as int);

    trust_vc::assert!(i2 == i3);
    trust_vc::assert!(i5 >= 0);
    trust_vc::assert!((n3 as int) + i6 == 0);
    trust_vc::assert!(i6 + (n3 as int) == 0);
    trust_vc::assert!((n3 as int) > i6);
    trust_vc::assert!(i6 < (n3 as int));
    trust_vc::assert!(x == 4);
}

#[trust_vc::ensures(true)]
fn test_literals_boundaries() {
    trust_vc::assert!(255u8 == 254u8 + 1);
    trust_vc::assert!(-128i8 == -127i8 - 1);
    trust_vc::assert!(127i8 == 126i8 + 1);
    trust_vc::assert!(i128::MIN < -127i128);
    trust_vc::assert!(i128::MAX > 127i128);
    trust_vc::assert!(u128::MAX > 255u128);
}

#[trust_vc::ensures(true)]
fn test_literals_fails_wrong_zero_boundary_counterexample() {
    trust_vc::assert!(0u8 == 255u8);
}

#[trust_vc::ensures(true)]
fn test_literals_fails_wrong_u8_boundary_counterexample() {
    trust_vc::assert!(255u8 == 254u8);
}

#[trust_vc::ensures(true)]
fn test_literals_fails_wrong_i8_low_boundary_counterexample() {
    trust_vc::assert!(-128i8 == -127i8);
}

#[trust_vc::ensures(true)]
fn test_literals_fails_wrong_i8_high_boundary_counterexample() {
    trust_vc::assert!(127i8 == 126i8);
}

#[trust_vc::spec]
fn large_int_sum_left() -> int {
    30_000_000_000_000_000_000_000i128 + 20_000_000_000_000_000_000_000i128
}

#[trust_vc::spec]
fn large_int_sum_right() -> int {
    20_000_000_000_000_000_000_000i128 + 30_000_000_000_000_000_000_000i128
}

#[trust_vc::spec]
fn large_int_difference() -> int {
    30_000_000_000_000_000_000_000i128 - 20_000_000_000_000_000_000_000i128
}

#[trust_vc::ensures(true)]
fn test_spec_const_like_large_arithmetic() {
    trust_vc::assert!(large_int_sum_left() == large_int_sum_right());
    trust_vc::assert!(large_int_sum_left() == 50_000_000_000_000_000_000_000i128);
    trust_vc::assert!(large_int_difference() == 10_000_000_000_000_000_000_000i128);
}

#[trust_vc::ensures(true)]
fn test_bool_to_int() {
    trust_vc::assert!(true as usize == 1);
    trust_vc::assert!(false as usize == 0);
    trust_vc::assert!(true as int == 1);
    trust_vc::assert!(false as int == 0);
}

#[trust_vc::ensures(true)]
fn test_enum_to_int_discriminant_constants() {
    trust_vc::assert!(IntegerCastEnum::A as usize == 0);
    trust_vc::assert!(IntegerCastEnum::B as usize == 255);
    trust_vc::assert!(IntegerCastEnum::C as usize == 256);
}

#[trust_vc::ensures(result == v as usize)]
#[trust_vc::ensures(result == 0 || result == 255 || result == 256)]
fn test_enum_to_int_symbolic_return(v: IntegerCastEnum) -> usize {
    v as usize
}

// Liar twins of upstream `test_enum_to_int` (2026-09-11): `C` is the implicit
// successor discriminant 256, and the symbolic cast ranges over all three.
#[trust_vc::ensures(true)]
fn test_enum_to_int_discriminant_liar_counterexample() {
    trust_vc::assert!(IntegerCastEnum::C as usize == 255);
}

#[trust_vc::ensures(result == 0 || result == 255)]
fn test_enum_to_int_symbolic_return_liar_counterexample(v: IntegerCastEnum) -> usize {
    v as usize
}

#[trust_vc::ensures(result == v as u8)]
fn test_enum_to_int_overflow_wrap(v: IntegerCastEnum) -> u8 {
    v as u8
}

#[trust_vc::ensures(true)]
fn test_finite_unsigned_to_nat_casts(u: u8, z: usize) {
    trust_vc::assert!((u as nat) >= 0);
    trust_vc::assert!((u as nat) < 256);
    trust_vc::assert!(add1_nat(u as nat) == (u as nat) + 1);
    trust_vc::assert!((z as nat) >= 0);
    trust_vc::assert!((z as nat) as int == z as int);
}

#[trust_vc::ensures(true)]
fn test_nat_to_finite_cast_wrap_constant() {
    let n: nat = 300;
    trust_vc::assert!(n as u8 == 44u8);
    trust_vc::assert!((n as u8) as nat == 44);
}

#[trust_vc::ensures(true)]
fn test_finite_signed_to_nat_cast_nonnegative() {
    let i: i8 = 5;
    trust_vc::assert!((i as nat) >= 0);
    trust_vc::assert!((i as nat) == 5);
}

#[trust_vc::ensures(true)]
fn test_finite_signed_to_nat_cast_fails_without_nonnegative(i: i8) {
    trust_vc::assert!((i as nat) as int == i as int);
}
