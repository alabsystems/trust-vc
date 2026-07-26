// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! P1-E (shifts cluster) soundness fixtures: fixed-width `<<`/`>>` must
//! wrap/truncate to the result width in two's complement, exactly like Rust.
//!
//! The historical hole: `lower_special` cross-coerced a suffixed `i32` left
//! operand to the (unsigned) shift-amount type, so a signed left shift onto the
//! sign bit folded to the out-of-range `+2^31` instead of `i32::MIN`, and a
//! signed `>>` lowered to a logical `bvlshr` rather than an arithmetic
//! `bvashr`. Ground truth is `rustc`: `1i32 << 31 == i32::MIN` (NOT a panic; the
//! sign bit lands on bit 31) and `-1i32 >> 1 == -1i32` (arithmetic shift).

// ── Left shift onto the sign bit: result is i32::MIN (< 0) ──────────────────

// FALSE: 1i32 << 31 == i32::MIN == -2147483648 < 0, so `result > 0` is false.
#[trust_vc::ensures(result > 0i32)]
fn ensures_shl31_gt0_FALSE() -> i32 {
    1i32 << 31u32
}

// TRUE companion: the returned value IS negative.
#[trust_vc::ensures(result < 0i32)]
fn ensures_shl31_lt0_TRUE() -> i32 {
    1i32 << 31u32
}

// TRUE: in-range left shift stays positive.
#[trust_vc::ensures(result > 0i32)]
fn ensures_shl30_gt0_TRUE() -> i32 {
    1i32 << 30u32
}

// ── Assert-level sign-bit-landing left shifts ──────────────────────────────

#[trust_vc::ensures(true)]
fn assert_shl31_gt0_FALSE() {
    trust_vc::assert!((1i32 << 31u32) > 0i32);
}

#[trust_vc::ensures(true)]
fn assert_2shl30_gt0_FALSE() {
    trust_vc::assert!((2i32 << 30u32) > 0i32);
}

#[trust_vc::ensures(true)]
fn assert_hexshl1_gt0_FALSE() {
    trust_vc::assert!((0x4000_0000i32 << 1u32) > 0i32);
}

// TRUE control: 1i32 << 30 is genuinely positive.
#[trust_vc::ensures(true)]
fn assert_shl30_gt0_TRUE() {
    trust_vc::assert!((1i32 << 30u32) > 0i32);
}

// Smoking-gun: the modeled value must be i32::MIN, not +2^31.
#[trust_vc::ensures(true)]
fn assert_shl31_as_int_eq_pos_FALSE() {
    trust_vc::assert!(((1i32 << 31u32) as int) == 2147483648int);
}

#[trust_vc::ensures(true)]
fn assert_shl31_as_int_eq_min_TRUE() {
    trust_vc::assert!(((1i32 << 31u32) as int) == -2147483648int);
}

#[trust_vc::ensures(true)]
fn assert_shl31_lt0_TRUE() {
    trust_vc::assert!((1i32 << 31u32) < 0i32);
}

// ── Signed right shift is arithmetic (sign-preserving) ─────────────────────

#[trust_vc::ensures(true)]
fn bv_shr_neg1_eq_logical_FALSE() {
    trust_vc::assert_by_bit_vector! { (-1i32 >> 1u32) == 0x7fff_ffffi32 };
}

#[trust_vc::ensures(true)]
fn bv_shr_neg1_eq_neg1_TRUE() {
    trust_vc::assert_by_bit_vector! { (-1i32 >> 1u32) == -1i32 };
}

#[trust_vc::ensures(true)]
fn bv_shr_neg4_eq_logical_FALSE() {
    trust_vc::assert_by_bit_vector! { (-4i32 >> 1u32) == 0x7fff_fffei32 };
}

#[trust_vc::ensures(true)]
fn bv_shr_neg4_eq_neg2_TRUE() {
    trust_vc::assert_by_bit_vector! { (-4i32 >> 1u32) == -2i32 };
}

// Unsigned right shift control (logical, unchanged): still verifies.
#[trust_vc::ensures(true)]
fn bv_shr_unsigned_TRUE() {
    trust_vc::assert_by_bit_vector! { (0xffff_ffffu32 >> 1u32) == 0x7fff_ffffu32 };
}

// bit_vector-mode left shift onto the sign bit is also FALSE.
#[trust_vc::ensures(true)]
fn bv_shl31_gt0_FALSE() {
    trust_vc::assert_by_bit_vector! { (1i32 << 31u32) > 0i32 };
}

// TRUE control: correct left-shift identity still verifies.
#[trust_vc::ensures(true)]
fn bv_shl3_eq_8_TRUE() {
    trust_vc::assert_by_bit_vector! { (1u64 << 3u32) == 8u64 };
}
