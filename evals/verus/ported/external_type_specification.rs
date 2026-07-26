// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/external_type_specification.rs`.
//
// TrustVc does not currently expose a Verus-style
// `external_type_specification` attribute for type proxy declarations. This
// file therefore pins the smallest Rust-valid behavior available today:
// - local transparent struct and enum source datatypes verify the same field
//   projection and variant payload facts that upstream proves through an
//   external type specification;
// - wrong transparent field and payload claims are rejected; and
// - an external std/core struct literal that would require imported external
//   type metadata fails closed instead of being treated as transparent.
//
// The broader upstream surface remains unsupported: proxy type declarations,
// duplicate proxy diagnostics, direct proxy-use diagnostics, visibility and
// generic-matching checks, external-body opaque datatype handling, recursive
// polarity annotations, builtin-type rejection, and vstd-imported std_specs are
// not claimed here.

pub const EXTERNAL_TYPE_SPECIFICATION_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "same_crate_struct_field_projection_verified",
        "test_basics::test same-crate external struct field projection",
        "verified",
        1,
    ),
    (
        "same_crate_enum_variant_payload_verified",
        "test_basics::test same-crate external enum payload projection",
        "verified",
        1,
    ),
    (
        "core_option_payload_projection_verified",
        "test_basics2::test / test_basics3::test core::option::Option payload projection",
        "verified",
        1,
    ),
    (
        "core_option_wrong_payload_counterexample",
        "test_basics2::test4 / test_basics3::test4 wrong Option payload projection",
        "counterexample",
        1,
    ),
    (
        "core_range_external_struct_literal_currently_errors",
        "test_basics2::test / test_basics3::test core::ops::Range field projection",
        "error",
        0,
    ),
];

pub fn external_type_specification_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXTERNAL_TYPE_SPECIFICATION_RS_EXPECTED_CASES
}

pub const EXTERNAL_TYPE_SPECIFICATION_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "core_range_external_struct_literal_currently_errors",
    &["struct literal for unknown type", "Range"],
)];

pub fn external_type_specification_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    EXTERNAL_TYPE_SPECIFICATION_RS_EXPECTED_ERROR_PATTERNS
}

struct ExternalTypeSpecStruct {
    t: u8,
}

enum ExternalTypeSpecEnum {
    One(u8),
    Two,
}

#[trust_vc::ensures(true)]
fn same_crate_struct_field_projection_verified() {
    let value = ExternalTypeSpecStruct { t: 5u8 };
    trust_vc::assert!(value.t == 5u8);
}

#[trust_vc::ensures(true)]
fn same_crate_struct_wrong_field_counterexample() {
    let value = ExternalTypeSpecStruct { t: 5u8 };
    trust_vc::assert!(value.t == 6u8);
}

#[trust_vc::ensures(true)]
fn same_crate_enum_variant_payload_verified() {
    let value = ExternalTypeSpecEnum::One(9u8);
    trust_vc::assert!(value.get_One_0() == 9u8);
    trust_vc::assert!(!value.is_Two());
}

#[trust_vc::ensures(true)]
fn same_crate_enum_wrong_payload_counterexample() {
    let value = ExternalTypeSpecEnum::One(9u8);
    trust_vc::assert!(value.get_One_0() == 8u8);
}

#[trust_vc::ensures(Option::<u8>::Some(5u8).unwrap() == 5u8)]
fn core_option_payload_projection_verified() {}

#[trust_vc::ensures(Option::<u8>::Some(5u8).unwrap() == 6u8)]
fn core_option_wrong_payload_counterexample() {}

#[trust_vc::ensures(true)]
fn core_range_external_struct_literal_currently_errors() {
    let range = core::ops::Range {
        start: 5u8,
        end: 7u8,
    };
    trust_vc::assert!(range.start == 5u8);
}
