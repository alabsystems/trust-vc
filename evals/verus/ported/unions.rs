// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/unions.rs`.
//
// The upstream file exercises Rust union active-variant reasoning, union field
// reads in exec and proof contexts, Verus `is_variant` and `get_union_field`
// builtins, union type aliases, generic unions, mode restrictions, recursive
// type checks, and visibility diagnostics. TrustVc does not currently model Rust
// union active-field state or Verus union builtins.
//
// This scout keeps the manifest entry `unsupported-gap` and records only stable
// evidence:
// - Rust-valid tagged-surrogate slices for the upstream x-active union cases;
// - one deterministic inactive-field counterexample; and
// - fail-closed native union and Verus-builtin boundaries.

#![allow(dead_code)]

#[derive(Clone, Copy, PartialEq, Eq)]
struct UnionsTagged {
    active_x: bool,
    x: u8,
    y: bool,
}

type UnionsAlias = UnionsTagged;
type UnionsAliasX = u8;

#[derive(Clone, Copy, PartialEq, Eq)]
struct UnionsGenericTagged<A: Copy, B: Copy> {
    active_x: bool,
    x: A,
    y: B,
}

union UnionsNative {
    x: u8,
    y: bool,
}

pub const UNIONS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "unions_tagged_x_basic_verified",
        "union_basic",
        "verified",
        5,
    ),
    (
        "unions_type_alias_x_constructor_verified",
        "union_basic",
        "verified",
        4,
    ),
    (
        "unions_generic_tagged_x_verified",
        "union_generics",
        "verified",
        4,
    ),
    (
        "unions_inactive_y_counterexample",
        "union_basic",
        "counterexample",
        2,
    ),
    (
        "unions_native_field_read_currently_blocked",
        "union_basic",
        "error",
        0,
    ),
    (
        "unions_native_pattern_currently_blocked",
        "union_pattern",
        "error",
        0,
    ),
    (
        "unions_get_union_field_currently_blocked",
        "get_union_field_bad_field_name",
        "error",
        0,
    ),
    (
        "unions_is_variant_currently_blocked",
        "union_basic",
        "error",
        0,
    ),
];

pub const UNIONS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "unions_native_field_read_currently_blocked",
        &["unsafe block", "unknown type", "unsupported"],
    ),
    (
        "unions_native_pattern_currently_blocked",
        &[
            "unsafe block",
            "using a union",
            "unsupported",
            "unresolved variable `x`",
        ],
    ),
    (
        "unions_get_union_field_currently_blocked",
        &["string literals are not yet supported", "get_union_field"],
    ),
    (
        "unions_is_variant_currently_blocked",
        &["string literals are not yet supported", "is_variant"],
    ),
];

pub fn unions_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    UNIONS_RS_EXPECTED_CASES
}

pub fn unions_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    UNIONS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn unions_tagged_x_basic_verified() {
    let u = UnionsTagged {
        active_x: true,
        x: 3u8,
        y: false,
    };
    let j = u.x;

    trust_vc::assert!(u.active_x);
    trust_vc::assert!(!u.y);
    trust_vc::assert!(j == 3u8);
    trust_vc::assert!(u.x == 3u8);
}

#[trust_vc::ensures(true)]
fn unions_type_alias_x_constructor_verified() {
    let active_x = true;
    let x: UnionsAliasX = 3u8;
    let y = false;

    trust_vc::assert!(active_x);
    trust_vc::assert!(x == 3u8);
    trust_vc::assert!(!y);
}

#[trust_vc::ensures(true)]
fn unions_generic_tagged_x_verified() {
    let u = UnionsGenericTagged::<u8, bool> {
        active_x: true,
        x: 3u8,
        y: false,
    };

    trust_vc::assert!(u.active_x);
    trust_vc::assert!(u.x == 3u8);
    trust_vc::assert!(!u.y);
}

#[trust_vc::ensures(true)]
fn unions_inactive_y_counterexample() {
    let y = false;

    trust_vc::assert!(y);
}

#[trust_vc::ensures(true)]
fn unions_native_field_read_currently_blocked() {
    let u = UnionsNative { x: 3u8 };
    let j = unsafe { u.x };

    trust_vc::assert!(j == 3u8);
}

#[trust_vc::ensures(true)]
fn unions_native_pattern_currently_blocked() {
    let u = UnionsNative { x: 3u8 };
    unsafe {
        let UnionsNative { x } = u;
        trust_vc::assert!(x == 3u8);
    }
}

#[trust_vc::ensures(true)]
fn unions_get_union_field_currently_blocked(u: UnionsNative) {
    trust_vc::assert!(get_union_field::<UnionsNative, u8>(u, "z") == 5u8);
}

#[trust_vc::ensures(true)]
fn unions_is_variant_currently_blocked(u: UnionsNative) {
    trust_vc::assert!(is_variant(u, "x"));
}
