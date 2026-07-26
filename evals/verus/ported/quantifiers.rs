// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream
// rust_verify_test/tests/quantifiers.rs.
//
// This file intentionally covers only the existential/quantifier shapes that
// have stable TrustVc evidence today. It does not claim parity for the full
// upstream file: map trigger regressions, broadcast forall, auto-trigger
// diagnostics, invalid-trigger diagnostic parity, generic quantified trigger
// cases, and the full assert-forall proof ecosystem remain unsupported.
// The nat-negative existential and missing-opaque-predicate existential below
// are retained for legacy/blocker visibility, but neither is promoted in the
// expected-case inventory because the current solver result is Unknown.

#![allow(dead_code)]

use trust_vc_types::{int, nat};

pub type QuantifiersExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type QuantifiersExpectedErrorPattern = (&'static str, &'static [&'static str]);

pub const QUANTIFIERS_RS_EXPECTED_CASES: &[QuantifiersExpectedCase] = &[
    ("test1", "", "verified", 2),
    ("simple_exists_witness", "", "verified", 1),
    ("simple_forall_reflexive", "", "verified", 1),
    (
        "inline_exists_nat_witness",
        "test1",
        "verified",
        1,
    ),
    (
        "opaque_predicate_ground_exists_verified",
        "",
        "verified",
        2,
    ),
    (
        "opaque_predicate_dual_forall_counterexample",
        "",
        "counterexample",
        2,
    ),
    ("test1_fails", "", "counterexample", 1),
    ("simple_forall_fails", "", "counterexample", 1),
    (
        "manual_trigger_expression_parity",
        "",
        "verified",
        1,
    ),
    (
        "invalid_trigger_without_bound_var_fails_closed",
        "",
        "error",
        0,
    ),
    ("forall_untyped_binder_fails_closed", "", "error", 0),
    ("exists_empty_binder_fails_closed", "", "error", 0),
    (
        "forall_unsupported_bound_type_fails_closed",
        "",
        "error",
        0,
    ),
    (
        "assert_forall_invalid_inner_trigger_attr_fails_closed",
        "assert_forall_invalid_attr",
        "error",
        0,
    ),
];

pub const QUANTIFIERS_RS_EXPECTED_ERROR_PATTERNS: &[QuantifiersExpectedErrorPattern] = &[
    (
        "invalid_trigger_without_bound_var_fails_closed",
        &["does not reference any bound variable"],
    ),
    (
        "forall_untyped_binder_fails_closed",
        &["requires an explicit type annotation", "'i'"],
    ),
    (
        "exists_empty_binder_fails_closed",
        &["at least one bound variable"],
    ),
    (
        "forall_unsupported_bound_type_fails_closed",
        &["Unsupported type", "Rc<i32>"],
    ),
    (
        "assert_forall_invalid_inner_trigger_attr_fails_closed",
        &["expected trigger attribute in assert forall"],
    ),
];

pub fn quantifiers_rs_expected_cases() -> &'static [QuantifiersExpectedCase] {
    QUANTIFIERS_RS_EXPECTED_CASES
}

pub fn quantifiers_rs_expected_error_patterns() -> &'static [QuantifiersExpectedErrorPattern] {
    QUANTIFIERS_RS_EXPECTED_ERROR_PATTERNS
}

fn exists<T, F>(_f: F) -> bool
where
    F: Fn(T) -> bool,
{
    true
}

fn forall<T, F>(_f: F) -> bool
where
    F: Fn(T) -> bool,
{
    true
}

#[trust_vc::opaque]
#[trust_vc::spec]
fn opaque_quant_tr(_i: int) -> bool {
    true
}

#[trust_vc::requires(ground == 300u32)]
#[trust_vc::ensures(true)]
fn test1(ground: u32) {
    trust_vc::assert!(ground == 300u32);
    trust_vc::assert!(exists(|i: u32| i > 300u32));
}

#[trust_vc::ensures(true)]
fn test1_fails() {
    trust_vc::assert!(exists(|i: u32| i > 0xffff_ffffu32));
}

#[trust_vc::ensures(true)]
fn simple_exists_witness() {
    trust_vc::assert!(exists(|i: i32| i == 0i32));
}

#[trust_vc::ensures(true)]
fn simple_forall_reflexive() {
    trust_vc::assert!(forall(|i: i32| i == i));
}

#[trust_vc::ensures(true)]
fn simple_forall_fails() {
    trust_vc::assert!(forall(|i: i32| i > 0i32));
}

#[trust_vc::ensures(true)]
fn inline_exists_nat_witness() {
    trust_vc::assert!(exists|i: nat| i == 0);
}

#[trust_vc::ensures(true)]
fn inline_exists_nat_negative_fails() {
    trust_vc::assert!(exists|i: nat| i < 0);
}

#[trust_vc::ensures(true)]
fn opaque_predicate_ground_exists_verified() {
    trust_vc::assume!(opaque_quant_tr(300));
    trust_vc::assert!(exists|i: nat| i >= 0 && opaque_quant_tr(i as int));
}

#[trust_vc::ensures(true)]
fn opaque_predicate_missing_ground_currently_unknown() {
    trust_vc::assume!(opaque_quant_tr(0) == opaque_quant_tr(0));
    trust_vc::assert!(exists|i: nat| i >= 0 && opaque_quant_tr(i as int));
}

#[trust_vc::ensures(true)]
fn opaque_predicate_dual_forall_counterexample() {
    trust_vc::assume!(opaque_quant_tr(300));
    trust_vc::assert!(forall|i: nat| !opaque_quant_tr(i as int));
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn manual_trigger_expression_parity() {
    trust_vc::assert!(forall(|i: i32| #[trigger] (i + 0i32 == i)));
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn invalid_trigger_without_bound_var_fails_closed() {
    trust_vc::assert_forall_by!(|i: int| #[trigger] (0 + 1) == 1 && i == i, {
        trust_vc::assume!(i == i);
    });
}

#[trust_vc::ensures(true)]
fn forall_untyped_binder_fails_closed() {
    trust_vc::assert!(forall(|i| i == i));
}

#[trust_vc::ensures(true)]
fn exists_empty_binder_fails_closed() {
    trust_vc::assert!(exists(|| true));
}

#[trust_vc::ensures(true)]
fn forall_unsupported_bound_type_fails_closed() {
    trust_vc::assert!(forall(|_item: Rc<i32>| true));
}

#[trust_vc::ensures(true)]
#[rustfmt::skip]
fn assert_forall_invalid_inner_trigger_attr_fails_closed() {
    trust_vc::assert_forall_by!(assert forall |k: int| #![autos] k == k by {});
}
