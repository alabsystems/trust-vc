// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/layout.rs`.
//
// The upstream file exercises Verus prelude layout axioms, explicit
// `global size_of`/`global layout` declarations, compile-time layout checking,
// primitive and pointer layout facts, alignment facts, and spec-only layout
// intrinsics. TrustVc does not currently expose those Verus layout declarations
// or diagnostic surfaces as executable replacement evidence.
//
// This scout slice keeps the upstream manifest entry unsupported-gap and pins
// only Rust-valid coverage:
// - Primitive associated constants and `usize`/`isize` target-width equality
//   verify through TrustVc's existing integer constant lowering.
// - A false pointer-width assertion must not verify.
// - Direct Rust `core::mem::size_of` and `align_of` primitive, fixed-array,
//   reference, and raw-pointer layout queries verify for the concrete surface
//   below.
// - User-defined repr(C) layout queries remain fail-closed until TrustVc has
//   replacement evidence for Verus `global layout` declarations.

#![allow(dead_code)]

pub const LAYOUT_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "layout_integer_constants_and_target_bits_verified",
        "constants",
        "verified",
        1,
    ),
    (
        "layout_core_mem_size_of_primitives_verified",
        "test_layouts_for_primitives",
        "verified",
        1,
    ),
    (
        "layout_core_mem_size_of_word_and_arrays_verified",
        "test_size_of_1",
        "verified",
        1,
    ),
    (
        "layout_core_mem_align_of_primitives_verified",
        "test_layouts_for_primitives",
        "verified",
        1,
    ),
    (
        "layout_core_mem_pointer_layout_verified",
        "test_ptr_layout",
        "verified",
        1,
    ),
    (
        "layout_pointer_width_sixteen_counterexample",
        "arch_fail_1",
        "counterexample",
        1,
    ),
    (
        "layout_core_mem_size_of_wrong_value_counterexample",
        "test_size_of_1",
        "counterexample",
        1,
    ),
    (
        "layout_core_mem_char_size_wrong_value_counterexample",
        "test_layouts_for_primitives",
        "counterexample",
        1,
    ),
    (
        "layout_core_mem_pointer_size_wrong_value_counterexample",
        "test_layouts_for_primitives",
        "counterexample",
        1,
    ),
    (
        "layout_core_mem_align_of_wrong_value_counterexample",
        "test_layouts_for_primitives",
        "counterexample",
        1,
    ),
    (
        "layout_core_mem_repr_c_struct_size_currently_blocked",
        "test_layout_3",
        "error",
        0,
    ),
    (
        "layout_core_mem_repr_c_struct_align_currently_blocked",
        "test_layout_3",
        "error",
        0,
    ),
    (
        "layout_core_mem_generic_repr_c_struct_size_currently_blocked",
        "test_layout_6",
        "error",
        0,
    ),
];

pub const LAYOUT_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "layout_core_mem_repr_c_struct_size_currently_blocked",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "layout_core_mem_repr_c_struct_align_currently_blocked",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "layout_core_mem_generic_repr_c_struct_size_currently_blocked",
        &["core::mem::size_of is only modeled"],
    ),
];

pub fn layout_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    LAYOUT_RS_EXPECTED_CASES
}

pub fn layout_rs_fail_closed_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    LAYOUT_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct LayoutTargetWitness {
    usize_bits: u32,
    isize_bits: u32,
    same_word_bits: bool,
}

#[repr(C)]
struct LayoutReprCStructWitness {
    v: u64,
    z: u32,
}

#[repr(C)]
struct LayoutGenericReprCStructWitness<V> {
    v: V,
    z: V,
}

#[trust_vc::ensures(true)]
fn layout_integer_constants_and_target_bits_verified() {
    let target = LayoutTargetWitness {
        usize_bits: usize::BITS,
        isize_bits: isize::BITS,
        same_word_bits: usize::BITS == isize::BITS,
    };
    let same_target = LayoutTargetWitness {
        usize_bits: usize::BITS,
        isize_bits: isize::BITS,
        same_word_bits: true,
    };

    trust_vc::assert!(u8::MIN == 0u8);
    trust_vc::assert!(u16::MIN == 0u16);
    trust_vc::assert!(u32::MIN == 0u32);
    trust_vc::assert!(u64::MIN == 0u64);
    trust_vc::assert!(u128::MIN == 0u128);
    trust_vc::assert!(usize::MIN == 0usize);
    trust_vc::assert!(u8::MAX == 255u8);
    trust_vc::assert!(u16::MAX == 0xffffu16);
    trust_vc::assert!(u32::MAX == 0xffff_ffffu32);
    trust_vc::assert!(u64::MAX == 0xffff_ffff_ffff_ffffu64);
    trust_vc::assert!(i8::MIN == -0x80i8);
    trust_vc::assert!(i16::MIN == -0x8000i16);
    trust_vc::assert!(i32::MIN == -0x8000_0000i32);
    trust_vc::assert!(i64::MIN == -0x8000_0000_0000_0000i64);
    trust_vc::assert!(i128::MIN < 0i128);
    trust_vc::assert!(isize::MIN < 0isize);
    trust_vc::assert!(i8::MAX == 0x7fi8);
    trust_vc::assert!(i16::MAX == 0x7fffi16);
    trust_vc::assert!(i32::MAX == 0x7fff_ffffi32);
    trust_vc::assert!(i64::MAX == 0x7fff_ffff_ffff_ffffi64);
    trust_vc::assert!(i128::MAX > 0i128);
    trust_vc::assert!(isize::MAX > 0isize);
    trust_vc::assert!(u8::BITS == 8u32);
    trust_vc::assert!(u16::BITS == 16u32);
    trust_vc::assert!(u32::BITS == 32u32);
    trust_vc::assert!(u64::BITS == 64u32);
    trust_vc::assert!(u128::BITS == 128u32);
    trust_vc::assert!(i8::BITS == 8u32);
    trust_vc::assert!(i16::BITS == 16u32);
    trust_vc::assert!(i32::BITS == 32u32);
    trust_vc::assert!(i64::BITS == 64u32);
    trust_vc::assert!(i128::BITS == 128u32);
    trust_vc::assert!(usize::BITS == 32u32 || usize::BITS == 64u32);
    trust_vc::assert!(isize::BITS == 32u32 || isize::BITS == 64u32);
    trust_vc::assert!(target.usize_bits == target.isize_bits);
    trust_vc::assert!(target.same_word_bits);
    trust_vc::assert!(target == same_target);
}

#[trust_vc::ensures(true)]
fn layout_pointer_width_sixteen_counterexample() {
    trust_vc::assert!(usize::BITS == 16u32);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_size_of_primitives_verified() {
    trust_vc::assert!(core::mem::size_of::<()>() == 0usize);
    trust_vc::assert!(core::mem::size_of::<bool>() == 1usize);
    trust_vc::assert!(core::mem::size_of::<char>() == 4usize);
    trust_vc::assert!(core::mem::size_of::<i8>() == 1usize);
    trust_vc::assert!(core::mem::size_of::<u8>() == 1usize);
    trust_vc::assert!(core::mem::size_of::<i16>() == 2usize);
    trust_vc::assert!(core::mem::size_of::<u16>() == 2usize);
    trust_vc::assert!(core::mem::size_of::<i32>() == 4usize);
    trust_vc::assert!(core::mem::size_of::<u32>() == 4usize);
    trust_vc::assert!(core::mem::size_of::<i64>() == 8usize);
    trust_vc::assert!(core::mem::size_of::<u64>() == 8usize);
    trust_vc::assert!(core::mem::size_of::<i128>() == 16usize);
    trust_vc::assert!(core::mem::size_of::<u128>() == 16usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_size_of_word_and_arrays_verified() {
    let word_bytes = core::mem::size_of::<usize>();
    trust_vc::assert!(word_bytes == 4usize || word_bytes == 8usize);
    trust_vc::assert!(core::mem::size_of::<isize>() == word_bytes);
    trust_vc::assert!(core::mem::size_of::<[u16; 3]>() == 6usize);
    trust_vc::assert!(core::mem::size_of::<[[u8; 2]; 3]>() == 6usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_size_of_wrong_value_counterexample() {
    trust_vc::assert!(core::mem::size_of::<u32>() == 2usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_char_size_wrong_value_counterexample() {
    trust_vc::assert!(core::mem::size_of::<char>() == 1usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_align_of_primitives_verified() {
    trust_vc::assert!(core::mem::align_of::<()>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<bool>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<u8>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<i8>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<u16>() == 2usize);
    trust_vc::assert!(core::mem::align_of::<i16>() == 2usize);
    trust_vc::assert!(core::mem::align_of::<u32>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<i32>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<char>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<[u16; 3]>() == core::mem::align_of::<u16>());
    trust_vc::assert!(core::mem::align_of::<[[u8; 2]; 3]>() == core::mem::align_of::<u8>());
}

#[trust_vc::ensures(true)]
fn layout_core_mem_pointer_layout_verified() {
    let word_bytes = core::mem::size_of::<usize>();

    trust_vc::assert!(core::mem::size_of::<*mut u8>() == core::mem::size_of::<*const u8>());
    trust_vc::assert!(core::mem::size_of::<*mut u8>() == core::mem::size_of::<&u8>());
    trust_vc::assert!(core::mem::align_of::<*mut u8>() == core::mem::align_of::<*const u8>());
    trust_vc::assert!(core::mem::align_of::<*mut u8>() == core::mem::align_of::<&u8>());
    trust_vc::assert!(core::mem::size_of::<*mut u8>() == word_bytes);
    trust_vc::assert!(core::mem::align_of::<*mut u8>() == core::mem::align_of::<usize>());
}

#[trust_vc::ensures(true)]
fn layout_core_mem_pointer_size_wrong_value_counterexample() {
    trust_vc::assert!(core::mem::size_of::<*const u8>() == 1usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_align_of_wrong_value_counterexample() {
    trust_vc::assert!(core::mem::align_of::<u32>() == 2usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_repr_c_struct_size_currently_blocked() {
    let struct_bytes = core::mem::size_of::<LayoutReprCStructWitness>();

    trust_vc::assert!(struct_bytes == 16usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_repr_c_struct_align_currently_blocked() {
    let struct_align = core::mem::align_of::<LayoutReprCStructWitness>();

    trust_vc::assert!(struct_align == 8usize);
}

#[trust_vc::ensures(true)]
fn layout_core_mem_generic_repr_c_struct_size_currently_blocked() {
    let struct_bytes = core::mem::size_of::<LayoutGenericReprCStructWitness<u64>>();

    trust_vc::assert!(struct_bytes == 16usize);
}
