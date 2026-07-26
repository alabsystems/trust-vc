// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/size_of.rs`.
//
// The upstream file exercises Verus `vstd::layout::size_of`, `align_of`,
// Sized/unsized distinctions, pointer metadata, tuple-layout non-assumptions,
// and target-semantics bounds. TrustVc does not currently expose those Verus
// layout intrinsics as replacement evidence.
//
// This scout keeps the manifest entry unsupported-gap and records only
// schema-ready evidence TrustVc can execute or reject today:
// - word-layout and record witnesses for the upstream thin-pointer/usize theme;
// - direct `core::mem::size_of`/`align_of` primitive, fixed-array, reference,
//   and raw-pointer facts;
// - stable counterexamples for false target, primitive, array, pointer, and
//   alignment claims; and
// - fail-closed Verus layout intrinsic plus DST slice metadata, tuple,
//   user-struct, Box/Rc/Arc boundaries.

#![allow(dead_code)]

pub const SIZE_OF_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "size_of_word_layout_surrogate_verified",
        "sizeof_test_thin_pointer_reference_same_word_size",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_primitive_sizes_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_array_sizes_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_thin_reference_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_raw_pointer_verified",
        "sizeof_test_pointer_layout_boundary",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_align_of_primitives_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_array_align_of_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_layout_record_witness_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_word_layout_sixteen_bit_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_primitive_size_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_array_size_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_reference_size_counterexample",
        "sizeof_test_ref_distinguished_core_size_of_boundary",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_raw_pointer_size_counterexample",
        "sizeof_test_false_raw_pointer_size_probe",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_align_of_counterexample",
        "sizeof_test_false_alignment_probe",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_array_align_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_verus_layout_size_of_intrinsic_currently_blocked",
        "sizeof_test",
        "error",
        0,
    ),
    (
        "size_of_verus_layout_align_of_intrinsic_currently_blocked",
        "sizeof_test",
        "error",
        0,
    ),
    (
        "size_of_core_mem_tuple_layout_currently_blocked",
        "sizeof_test_tuple_wrong_concrete_tuple_layout_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_struct_layout_currently_blocked",
        "sized_trait_broadcast_concrete_user_struct_layout_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_tuple_align_currently_blocked",
        "sizeof_test_tuple_align_concrete_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_struct_align_currently_blocked",
        "sized_trait_broadcast_concrete_user_struct_align_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_box_rc_arc_layout_currently_blocked",
        "sizeof_test_box_rc_arc_distinguished_boundaries",
        "error",
        0,
    ),
    (
        "size_of_core_mem_slice_size_of_val_currently_blocked",
        "pointee_metadata",
        "error",
        0,
    ),
];

pub const SIZE_OF_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "size_of_verus_layout_size_of_intrinsic_currently_blocked",
        &["unknown return type", "vstd::layout::size_of"],
    ),
    (
        "size_of_verus_layout_align_of_intrinsic_currently_blocked",
        &["unknown return type", "vstd::layout::align_of"],
    ),
    (
        "size_of_core_mem_tuple_layout_currently_blocked",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_struct_layout_currently_blocked",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_tuple_align_currently_blocked",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "size_of_core_mem_struct_align_currently_blocked",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "size_of_core_mem_box_rc_arc_layout_currently_blocked",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_slice_size_of_val_currently_blocked",
        &["unknown return type", "core::mem::size_of_val"],
    ),
];

pub fn size_of_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SIZE_OF_RS_EXPECTED_CASES
}

pub fn size_of_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    SIZE_OF_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SizeOfWordLayoutWitness {
    pointer_bits: u32,
    usize_bits: u32,
    thin_pointer_word_sized: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SizeOfPrimitiveLayoutWitness {
    unit_size: usize,
    bool_size: usize,
    char_size: usize,
    u128_size: usize,
    f64_size: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SizeOfLayoutRecordWitness {
    size_bytes: usize,
    align_bytes: usize,
    zero_sized: bool,
    word_sized: bool,
}

#[repr(C)]
struct SizeOfReprCStructWitness {
    tag: u8,
    count: u32,
}

#[trust_vc::ensures(true)]
fn size_of_word_layout_surrogate_verified() {
    let witness = SizeOfWordLayoutWitness {
        pointer_bits: usize::BITS,
        usize_bits: usize::BITS,
        thin_pointer_word_sized: true,
    };
    let same_witness = SizeOfWordLayoutWitness {
        pointer_bits: usize::BITS,
        usize_bits: usize::BITS,
        thin_pointer_word_sized: usize::BITS == usize::BITS,
    };

    trust_vc::assert!(usize::BITS == 32u32 || usize::BITS == 64u32);
    trust_vc::assert!(isize::BITS == usize::BITS);
    trust_vc::assert!(witness.pointer_bits == witness.usize_bits);
    trust_vc::assert!(witness.thin_pointer_word_sized);
    trust_vc::assert!(witness == same_witness);
}

#[trust_vc::ensures(true)]
fn size_of_word_layout_sixteen_bit_counterexample() {
    trust_vc::assert!(usize::BITS == 16u32);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_primitive_sizes_verified() {
    let witness = SizeOfPrimitiveLayoutWitness {
        unit_size: core::mem::size_of::<()>(),
        bool_size: core::mem::size_of::<bool>(),
        char_size: core::mem::size_of::<char>(),
        u128_size: core::mem::size_of::<u128>(),
        f64_size: core::mem::size_of::<f64>(),
    };
    let expected = SizeOfPrimitiveLayoutWitness {
        unit_size: 0usize,
        bool_size: 1usize,
        char_size: 4usize,
        u128_size: 16usize,
        f64_size: 8usize,
    };

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
    trust_vc::assert!(core::mem::size_of::<f32>() == 4usize);
    trust_vc::assert!(core::mem::size_of::<f64>() == 8usize);
    trust_vc::assert!(core::mem::size_of::<isize>() == core::mem::size_of::<usize>());
    trust_vc::assert!(witness == expected);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_array_sizes_verified() {
    let word_bytes = core::mem::size_of::<usize>();

    trust_vc::assert!(core::mem::size_of::<[u16; 3]>() == 6usize);
    trust_vc::assert!(core::mem::size_of::<[[u8; 2]; 3]>() == 6usize);
    trust_vc::assert!(core::mem::size_of::<[u32; 0]>() == 0usize);
    trust_vc::assert!(core::mem::size_of::<[(); 8]>() == 0usize);
    trust_vc::assert!(core::mem::size_of::<[&u8; 2]>() == word_bytes * 2usize);
    trust_vc::assert!(core::mem::size_of::<[*const u16; 2]>() == word_bytes * 2usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_thin_reference_verified(value: &u8) {
    let reference_bytes = core::mem::size_of::<&u8>();
    let mutable_reference_bytes = core::mem::size_of::<&mut u16>();
    let word_bytes = core::mem::size_of::<usize>();

    trust_vc::assert!(*value == *value);
    trust_vc::assert!(reference_bytes == word_bytes);
    trust_vc::assert!(mutable_reference_bytes == word_bytes);
    trust_vc::assert!(core::mem::size_of::<&&u8>() == word_bytes);
    trust_vc::assert!(core::mem::align_of::<&u8>() == core::mem::align_of::<usize>());
    trust_vc::assert!(core::mem::align_of::<&mut u16>() == core::mem::align_of::<usize>());
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_raw_pointer_verified() {
    let word_bytes = core::mem::size_of::<usize>();
    let reference_bytes = core::mem::size_of::<&u8>();
    let const_pointer_bytes = core::mem::size_of::<*const u8>();
    let mut_pointer_bytes = core::mem::size_of::<*mut u16>();

    trust_vc::assert!(reference_bytes == word_bytes);
    trust_vc::assert!(const_pointer_bytes == word_bytes);
    trust_vc::assert!(mut_pointer_bytes == word_bytes);
    trust_vc::assert!(core::mem::align_of::<&u8>() == core::mem::align_of::<*const u8>());
    trust_vc::assert!(core::mem::align_of::<*const u8>() == core::mem::align_of::<*mut u16>());
    trust_vc::assert!(core::mem::align_of::<*const u8>() == core::mem::align_of::<usize>());
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_align_of_primitives_verified() {
    trust_vc::assert!(core::mem::align_of::<()>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<bool>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<char>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<i8>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<u8>() == 1usize);
    trust_vc::assert!(core::mem::align_of::<i16>() == 2usize);
    trust_vc::assert!(core::mem::align_of::<u16>() == 2usize);
    trust_vc::assert!(core::mem::align_of::<i32>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<u32>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<f32>() == 4usize);
    trust_vc::assert!(core::mem::align_of::<isize>() == core::mem::align_of::<usize>());
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_array_align_of_verified() {
    trust_vc::assert!(core::mem::align_of::<[u16; 3]>() == core::mem::align_of::<u16>());
    trust_vc::assert!(core::mem::align_of::<[u32; 0]>() == core::mem::align_of::<u32>());
    trust_vc::assert!(core::mem::align_of::<[[u8; 2]; 3]>() == core::mem::align_of::<u8>());
    trust_vc::assert!(core::mem::align_of::<[&u8; 2]>() == core::mem::align_of::<&u8>());
}

#[trust_vc::ensures(true)]
fn size_of_layout_record_witness_verified() {
    let unit_layout = SizeOfLayoutRecordWitness {
        size_bytes: core::mem::size_of::<()>(),
        align_bytes: core::mem::align_of::<()>(),
        zero_sized: true,
        word_sized: false,
    };
    let reference_layout = SizeOfLayoutRecordWitness {
        size_bytes: core::mem::size_of::<&u8>(),
        align_bytes: core::mem::align_of::<&u8>(),
        zero_sized: false,
        word_sized: true,
    };
    let array_layout = SizeOfLayoutRecordWitness {
        size_bytes: core::mem::size_of::<[u16; 3]>(),
        align_bytes: core::mem::align_of::<[u16; 3]>(),
        zero_sized: false,
        word_sized: false,
    };

    trust_vc::assert!(unit_layout.size_bytes == 0usize);
    trust_vc::assert!(unit_layout.align_bytes == 1usize);
    trust_vc::assert!(unit_layout.zero_sized);
    trust_vc::assert!(unit_layout.word_sized == false);
    trust_vc::assert!(reference_layout.size_bytes == core::mem::size_of::<usize>());
    trust_vc::assert!(reference_layout.align_bytes == core::mem::align_of::<usize>());
    trust_vc::assert!(reference_layout.zero_sized == false);
    trust_vc::assert!(reference_layout.word_sized);
    trust_vc::assert!(array_layout.size_bytes == 6usize);
    trust_vc::assert!(array_layout.align_bytes == 2usize);
    trust_vc::assert!(array_layout.zero_sized == false);
    trust_vc::assert!(array_layout.word_sized == false);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_primitive_size_counterexample() {
    trust_vc::assert!(core::mem::size_of::<char>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_array_size_counterexample() {
    trust_vc::assert!(core::mem::size_of::<[u16; 3]>() == 4usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_reference_size_counterexample() {
    trust_vc::assert!(core::mem::size_of::<&u8>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_raw_pointer_size_counterexample() {
    trust_vc::assert!(core::mem::size_of::<*const u8>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_align_of_counterexample() {
    trust_vc::assert!(core::mem::align_of::<u32>() == 2usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_wrong_array_align_counterexample() {
    trust_vc::assert!(core::mem::align_of::<[u16; 3]>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_verus_layout_size_of_intrinsic_currently_blocked() {
    trust_vc::assert!(vstd::layout::size_of::<u8>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_verus_layout_align_of_intrinsic_currently_blocked() {
    trust_vc::assert!(vstd::layout::align_of::<u8>() == 1usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_slice_size_of_val_currently_blocked(value: &[u8]) {
    let bytes = core::mem::size_of_val(value);

    trust_vc::assert!(bytes == value.len());
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_tuple_layout_currently_blocked() {
    let tuple_bytes = core::mem::size_of::<(u8, u16)>();

    trust_vc::assert!(tuple_bytes == 4usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_struct_layout_currently_blocked() {
    let struct_bytes = core::mem::size_of::<SizeOfReprCStructWitness>();

    trust_vc::assert!(struct_bytes == 8usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_tuple_align_currently_blocked() {
    let tuple_align = core::mem::align_of::<(u8, u16)>();

    trust_vc::assert!(tuple_align == 2usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_struct_align_currently_blocked() {
    let struct_align = core::mem::align_of::<SizeOfReprCStructWitness>();

    trust_vc::assert!(struct_align == 4usize);
}

#[trust_vc::ensures(true)]
fn size_of_core_mem_box_rc_arc_layout_currently_blocked() {
    let box_bytes = core::mem::size_of::<Box<u8>>();
    let rc_bytes = core::mem::size_of::<std::rc::Rc<u8>>();
    let arc_bytes = core::mem::size_of::<std::sync::Arc<u8>>();

    trust_vc::assert!(box_bytes == core::mem::size_of::<usize>());
    trust_vc::assert!(rc_bytes == core::mem::size_of::<usize>());
    trust_vc::assert!(arc_bytes == core::mem::size_of::<usize>());
}
