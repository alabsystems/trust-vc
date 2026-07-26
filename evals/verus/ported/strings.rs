// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream
// `rust_verify_test/tests/strings.rs`.
//
// This file intentionally covers only a smallest supported slice:
// - exact Rust runtime behavior for std str/String length, equality, ascii
//   checks, and append-like push_str;
// - exact TrustVc char literal equality/inequality from upstream
//   `test_char_passes` / `test_char_fails`;
// - exact string-literal equality/disequality via ay's native `Sort::String`
//   (`str_literal_equality_verified`);
// - the current default TrustVc `String::view()` length/equality surface; and
// - a fail-closed guard documenting that direct `String::len()` is not part of
//   this default extraction slice.
//
// Full strings.rs parity remains blocked on reveal_strlit, exact string-literal
// views, String::from_str view equality, is_ascii proofs, get_char/get_ascii,
// unicode_len, substring_ascii/substring_char, byte views, append/concat view
// postconditions, chars iterators, and String deref behavior.

#![allow(dead_code, unused_variables)]

use trust_vc_types::View;

pub const STRINGS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test_char_passes_ascii_literal_verified",
        "test_char_passes",
        "verified",
        2,
    ),
    (
        "test_char_fails_ascii_literal_counterexample",
        "test_char_fails",
        "counterexample",
        1,
    ),
    (
        "string_view_len_reflexive_verified",
        "test_passes_len",
        "verified",
        1,
    ),
    (
        "string_view_equality_reflexive_verified",
        "test_string_1_pass/test_strlit_neq equality surrogate",
        "verified",
        1,
    ),
    (
        "str_literal_equality_verified",
        "test_strlit_neq/test_string_1_pass literal equality boundary",
        "verified",
        1,
    ),
    (
        "string_direct_len_fail_closed_error",
        "test_passes_len",
        "error",
        0,
    ),
];

pub const STRINGS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    // NOTE: literal string equality is now VERIFIED (ay native `Sort::String`),
    // so `str_literal_equality_verified` is no longer a fail-closed error case.
    // Direct `String::len()` (no `view()`) still fails closed by design.
    (
        "string_direct_len_fail_closed_error",
        &["len on 'String'", "view()"],
    ),
];

pub fn strings_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    STRINGS_RS_EXPECTED_CASES
}

pub fn strings_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    STRINGS_RS_EXPECTED_ERROR_PATTERNS
}

pub fn test_passes_len_runtime_std_str() {
    let x = "abcdef";
    assert_eq!(x.len(), 6);
    assert_eq!(x.chars().count(), 6);
}

pub fn test_fails_len_runtime_wrong_counterexample() {
    let x = "abcdef";
    assert_eq!(x.len(), 1);
}

pub fn test_pass_is_ascii_runtime_std_str() {
    let x = "Hello World";
    assert!(x.is_ascii());
}

pub fn test_fails_is_ascii_runtime_wrong_counterexample() {
    let x = "\u{00e0}";
    assert!(x.is_ascii());
}

pub fn test_append_1_runtime_std_string_push_str() {
    let mut s = String::from("hello ");
    s.push_str("world");
    assert_eq!(s, "hello world");
    assert!(s.is_ascii());
}

pub fn test_str_and_string_eq_runtime_std_subset() {
    let x = "Hello World";
    let y = "Hello World";
    let z = "Gello World";
    assert_eq!(x, y);
    assert_ne!(x, z);

    let owned = String::from("Hello World");
    assert_eq!(owned.as_str(), x);
    assert_eq!(owned, x);
}

pub fn test_fails_string_eq_runtime_wrong_counterexample() {
    let owned = String::from("Hello World");
    assert_eq!(owned, "Gello World");
}

fn test_char_passes_ascii_literal_verified() {
    let c = 'c';
    trust_vc::assert!(c == 'c');
    trust_vc::assert!(c != 'b');
}

fn test_char_fails_ascii_literal_counterexample() {
    let c = 'c';
    trust_vc::assert!(c == 'a');
}

fn string_view_len_reflexive_verified(s: String) {
    trust_vc::assert!(s.view().len() == s.view().len());
}

fn string_view_equality_reflexive_verified(s: String) {
    trust_vc::assert!(s.view() == s.view());
}

fn string_view_len_irreflexive_currently_unknown(s: String) {
    trust_vc::assert!(s.view().len() != s.view().len());
}

fn string_view_equality_irreflexive_currently_unknown(s: String) {
    trust_vc::assert!(s.view() != s.view());
}

fn str_literal_equality_verified() {
    // `let`-bound string literals lower to ay's native `Sort::String` constants,
    // so equality of two identical literals is decided sound (VERIFIED). Distinct
    // literals would COUNTEREXAMPLE.
    let x = "Hello World";
    let y = "Hello World";
    trust_vc::assert!(x == y);
}

fn string_view_len_inconsistent_currently_unknown(s: String) {
    trust_vc::assume!(s.view().len() == 6usize);
    trust_vc::assert!(s.view().len() == 1usize);
}

fn string_direct_len_fail_closed_error(s: String) {
    trust_vc::assert!(s.len() == s.len());
}
