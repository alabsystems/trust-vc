// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/eq_cmp.rs`.
//
// The upstream file proves Eq/Ord/PartialEq/PartialOrd laws through vstd law
// specs, trait-method calls, custom PartialEq implementations, and structural
// equality. TrustVc does not currently expose those vstd law/spec surfaces as
// executable replacement evidence.
//
// This scout slice keeps the upstream manifest entry unsupported-gap and pins
// only Rust-valid coverage:
// - Primitive ordering and derived structural equality verify through operators.
// - Primitive PartialOrd::{lt, gt} method lowering verifies.
// - A concrete `u8` order-to-equality helper mirrors upstream `test_eq`.
// - Primitive branch witnesses mirror the upstream `test_eq`/`test_eq_wrong`
//   order/equality shape.
// - Concrete Option equality and finite-integer PartialOrd witnesses mirror the
//   upstream `test` calls.
// - False primitive, helper-contract, derived-structural, and order-branch
//   assertions produce counterexamples.
// - Concrete custom-PartialEq operator evidence mirrors upstream `test_p_ee`.
// - Current fail-closed unsupported cases publish stable expected_error_patterns.
// - Generic Ord/vstd law specs, non-integer/generic Option PartialOrd methods,
//   direct structural `.eq` calls, and custom PartialEq implementation calls
//   remain fail-closed.

#![allow(
    clippy::if_same_then_else,
    clippy::needless_bool,
    dead_code,
    unused_variables
)]

pub type EqCmpRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type EqCmpRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const EQ_CMP_RS_EXPECTED_CASES: &[EqCmpRsExpectedCase] = &[
    (
        "eq_cmp_structural_equality_and_primitive_order_verified",
        "eq_cmp1",
        "verified",
        6,
    ),
    (
        "eq_cmp_literal_order_counterexample",
        "eq_cmp1",
        "counterexample",
        1,
    ),
    (
        "eq_cmp_partial_ord_lt_method_verified",
        "eq_cmp1",
        "verified",
        1,
    ),
    (
        "eq_cmp_partial_ord_gt_method_verified",
        "eq_cmp1",
        "verified",
        1,
    ),
    (
        "eq_cmp_partial_ord_gt_method_counterexample",
        "eq_cmp1",
        "counterexample",
        1,
    ),
    (
        "eq_cmp_u8_order_to_eq_helper_verified",
        "eq_cmp1::test_eq",
        "verified",
        1,
    ),
    (
        "eq_cmp_u8_order_to_eq_helper_call_verified",
        "eq_cmp1::test",
        "verified",
        1,
    ),
    (
        "eq_cmp_primitive_order_branch_equality_verified",
        "eq_cmp1",
        "verified",
        1,
    ),
    (
        "eq_cmp_primitive_order_wrong_branch_counterexample",
        "eq_cmp1::test_eq_wrong",
        "counterexample",
        1,
    ),
    (
        "eq_cmp_option_equality_witnesses_verified",
        "eq_cmp1",
        "verified",
        2,
    ),
    (
        "eq_cmp_structural_tuple_operator_verified",
        "eq_cmp1",
        "verified",
        2,
    ),
    (
        "eq_cmp_structural_tuple_eq_method_verified",
        "eq_cmp1::check_eq",
        "verified",
        3,
    ),
    (
        "eq_cmp_structural_tuple_eq_method_liar_counterexample",
        "eq_cmp1::check_eq",
        "counterexample",
        2,
    ),
    (
        "eq_cmp_option_partial_ord_method_verified",
        "eq_cmp1::test_eq<Option<u8>>",
        "verified",
        1,
    ),
    (
        "eq_cmp_option_order_to_eq_helper_verified",
        "eq_cmp1::test",
        "verified",
        1,
    ),
    (
        "eq_cmp_custom_partial_eq_method_verified",
        "eq_cmp1::test_p_eq",
        "verified",
        2,
    ),
    (
        "eq_cmp_custom_partial_eq_method_liar_counterexample",
        "eq_cmp1::test_p_eq",
        "counterexample",
        2,
    ),
    (
        "eq_cmp_custom_partial_eq_operator_verified",
        "eq_cmp1::test_p_ee",
        "verified",
        1,
    ),
    (
        "eq_cmp_custom_partial_eq_operator_liar_counterexample",
        "eq_cmp1::test_p_ee",
        "counterexample",
        1,
    ),
];

pub const EQ_CMP_RS_EXPECTED_ERROR_PATTERNS: &[EqCmpRsExpectedErrorPatterns] = &[];

pub fn eq_cmp_rs_expected_cases() -> &'static [EqCmpRsExpectedCase] {
    EQ_CMP_RS_EXPECTED_CASES
}

pub fn eq_cmp_rs_expected_error_patterns() -> &'static [EqCmpRsExpectedErrorPatterns] {
    EQ_CMP_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct EqCmpRecord {
    value: u8,
    flag: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct EqCmpTuple(u8, bool);

#[derive(Clone, Copy, Eq)]
struct EqCmpCustomPartialEq(u8, bool);

impl PartialEq for EqCmpCustomPartialEq {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

fn eq_cmp_structural_equality_and_primitive_order_verified(value: u8) {
    let left = EqCmpRecord { value, flag: true };
    let same = EqCmpRecord { value, flag: true };
    let different_flag = EqCmpRecord { value, flag: false };

    trust_vc::assert!(left == same);
    trust_vc::assert!(left != different_flag);
    trust_vc::assert!(value <= value);
    trust_vc::assert!(value >= value);
    trust_vc::assert!(3u8 < 5u8);
    trust_vc::assert!(5u8 > 3u8);
}

fn eq_cmp_literal_order_counterexample() {
    trust_vc::assert!(5u8 < 3u8);
}

fn eq_cmp_partial_ord_lt_method_verified(left: u8, right: u8) {
    let result = left.lt(&right);

    trust_vc::assert!(result == (left < right));
}

fn eq_cmp_partial_ord_gt_method_verified(left: u8, right: u8) {
    let result = left.gt(&right);

    trust_vc::assert!(result == (left > right));
}

fn eq_cmp_partial_ord_gt_method_counterexample() {
    let lower = 3u8;
    let higher = 5u8;

    trust_vc::assert!(lower.gt(&higher));
}

#[trust_vc::contract(
    returns(result),
    ensures(result == (left == right)),
)]
fn eq_cmp_u8_order_to_eq_helper(left: u8, right: u8) -> bool {
    if left.lt(&right) {
        return false;
    }
    if left.gt(&right) {
        return false;
    }
    true
}

fn eq_cmp_u8_order_to_eq_helper_verified(left: u8, right: u8) {
    let result = if left.lt(&right) {
        false
    } else if left.gt(&right) {
        false
    } else {
        true
    };

    trust_vc::assert!(result == (left == right));
}

fn eq_cmp_u8_order_to_eq_helper_call_verified(left: u8, right: u8) {
    let result = eq_cmp_u8_order_to_eq_helper(left, right);

    trust_vc::assert!(result == (left == right));
}

fn eq_cmp_primitive_order_branch_equality_verified(left: u8, right: u8) {
    let result = if left.lt(&right) {
        false
    } else if left.gt(&right) {
        false
    } else {
        true
    };

    trust_vc::assert!(result == (left == right));
}

fn eq_cmp_primitive_order_wrong_branch_counterexample() {
    let left = 5u8;
    let right = 3u8;

    trust_vc::assert!(!left.gt(&right));
}

fn eq_cmp_option_equality_witnesses_verified() {
    let same_left = Some(5u8);
    let same_right = Some(4u8 + 1u8);
    let lower = Some(4u8 - 1u8);

    trust_vc::assert!(same_left == same_right);
    trust_vc::assert!(same_left != lower);
}

fn eq_cmp_option_partial_ord_method_verified() {
    let left = Some(5u8);
    let right = Some(4u8 - 1u8);

    trust_vc::assert!(left.gt(&right));
}

fn eq_cmp_option_order_to_eq_helper_verified(left: Option<u8>, right: Option<u8>) {
    let result = if left.lt(&right) {
        false
    } else if left.gt(&right) {
        false
    } else {
        true
    };

    trust_vc::assert!(result == (left == right));
}

fn eq_cmp_structural_tuple_operator_verified() {
    let left = EqCmpTuple(3u8, true);
    let same = EqCmpTuple(3u8, true);
    let different = EqCmpTuple(3u8, false);

    trust_vc::assert!(left == same);
    trust_vc::assert!(left != different);
}

fn eq_cmp_structural_tuple_eq_method_verified() {
    let left = EqCmpTuple(3u8, true);
    let same = EqCmpTuple(3u8, true);
    let different = EqCmpTuple(3u8, false);

    trust_vc::assert!(left.eq(&same));
    trust_vc::assert!(!left.eq(&different));
}

// Liar twin of upstream `check_eq` (2026-09-11): the derived `PartialEq::eq`
// method is structural, so `left.eq(&different)` is refuted.
fn eq_cmp_structural_tuple_eq_method_liar_counterexample() {
    let left = EqCmpTuple(3u8, true);
    let different = EqCmpTuple(3u8, false);

    trust_vc::assert!(left.eq(&different));
}

fn eq_cmp_custom_partial_eq_method_verified() {
    let left = EqCmpCustomPartialEq(3u8, true);
    let different = EqCmpCustomPartialEq(3u8, false);

    trust_vc::assert!(!left.eq(&different));
}

// Liar twin of upstream `test_p_eq` (2026-09-11): the hand-written `eq` body
// (`self.0 == other.0 && self.1 == other.1`) is what the call means, so
// `left.eq(&different)` is refuted.
fn eq_cmp_custom_partial_eq_method_liar_counterexample() {
    let left = EqCmpCustomPartialEq(3u8, true);
    let different = EqCmpCustomPartialEq(3u8, false);

    trust_vc::assert!(left.eq(&different));
}

// Upstream `test_p_ee` (VERIFIED again 2026-09-11): the `!=` OPERATOR on a datatype
// with a hand-written `PartialEq` lowers to the impl's own `eq` (as `!eq`, or the
// written `ne`) — the same inherent-method axiom the `.eq()` method call uses —
// so the structural gate of 2026-07-24 no longer refuses it.
fn eq_cmp_custom_partial_eq_operator_verified() {
    let left = EqCmpCustomPartialEq(3u8, true);
    let different = EqCmpCustomPartialEq(3u8, false);

    trust_vc::assert!(left != different);
}

// Liar twin: `==` of those two is refuted under the field-wise custom body.
fn eq_cmp_custom_partial_eq_operator_liar_counterexample() {
    let left = EqCmpCustomPartialEq(3u8, true);
    let different = EqCmpCustomPartialEq(3u8, false);

    trust_vc::assert!(left == different);
}
