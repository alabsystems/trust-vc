// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/lifetime.rs`.
//
// This scout covers Rust-valid slices TrustVc can express today:
// - Consuming a non-Copy value exactly once.
// - Splitting a moved struct into independently consumed fields.
// - Read-only mutable borrows of two distinct locals and sequential mutable
//   borrows of one local.
// - Named-lifetime reference identity through a valid same-lifetime caller.
// - Copy payloads that can be reused after being passed by value.
// - Direct scalar writes through local mutable references.
// - Stable false-tail counterexamples for upstream negative-case shapes.
// - Fail-closed boundaries for reborrow writeback and compound dereference
//   assignment.
//
// Upstream lifetime.rs remains an unsupported gap: most source cases exercise
// Verus tracked/proof/ghost modes, Rust compiler lifetime diagnostics, and
// mode-aware move checking that are not directly executable TrustVc evidence.

#![allow(dead_code)]

#[derive(PartialEq, Eq)]
struct LifetimeToken {
    value: u64,
}

struct LifetimePair {
    left: LifetimeToken,
    right: LifetimeToken,
}

struct LifetimeRefHolder<'a> {
    value: &'a u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct LifetimeCopyToken {
    value: u64,
}

fn consume_token(_token: LifetimeToken) {}

fn consume_copy_token(_token: LifetimeCopyToken) {}

fn borrow_two_values(_first: &mut u64, _second: &mut u64) {}

fn borrow_one_value(_value: &mut u64) {}

pub const LIFETIME_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("lifetime_consume_once", "consume_once", "verified", 1),
    (
        "lifetime_consume_fields_ok",
        "consume_fields_ok",
        "verified",
        1,
    ),
    (
        "lifetime_borrow_two_distinct_locals_ok",
        "borrow_local_ok",
        "verified",
        1,
    ),
    ("lifetime_sequential_mutable_borrows_ok", "", "verified", 1),
    (
        "lifetime_return_ref_named_identity",
        "return_wrong_lifetime1",
        "verified",
        1,
    ),
    (
        "lifetime_return_ref_named_identity_caller",
        "return_wrong_lifetime1",
        "verified",
        1,
    ),
    ("lifetime_shared_ref_read_verified", "", "verified", 1),
    (
        "lifetime_ref_holder_named_identity_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "lifetime_copy_payload_reuse_ok",
        "lifetime_copy_succeed",
        "verified",
        1,
    ),
    (
        "lifetime_mutable_reference_scalar_write_verified",
        "",
        "verified",
        1,
    ),
    (
        "lifetime_mutable_reference_write_currently_blocked",
        "tracked_borrow_mut_assignment",
        "verified",
        1,
    ),
    (
        "lifetime_false_assert_counterexample",
        "two_phase",
        "counterexample",
        1,
    ),
    (
        "lifetime_assign_twice_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "lifetime_mutable_reference_scalar_write_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "lifetime_compound_mutable_reference_assignment_verified",
        "",
        "verified",
        4,
    ),
];

pub const LIFETIME_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "lifetime_ref_holder_named_identity_currently_blocked",
        &["field 'value'", "specification context"],
    ),
];

pub fn lifetime_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    LIFETIME_RS_EXPECTED_CASES
}

pub fn lifetime_rs_fail_closed_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    LIFETIME_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::requires(value == 12u64)]
#[trust_vc::ensures(true)]
fn lifetime_consume_once(value: u64) {
    let token = LifetimeToken { value };
    consume_token(token);
    trust_vc::assert!(value == 12u64);
}

#[trust_vc::ensures(true)]
fn lifetime_consume_fields_ok() {
    let pair = LifetimePair {
        left: LifetimeToken { value: 12u64 },
        right: LifetimeToken { value: 13u64 },
    };

    consume_token(pair.left);
    consume_token(pair.right);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn lifetime_borrow_two_distinct_locals_ok() {
    let mut first = 12u64;
    let mut second = 13u64;

    borrow_two_values(&mut first, &mut second);
    trust_vc::assert!(true);
}

#[trust_vc::requires(value == 12u64)]
#[trust_vc::ensures(true)]
fn lifetime_sequential_mutable_borrows_ok(value: u64) {
    let mut local = value;

    borrow_one_value(&mut local);
    borrow_one_value(&mut local);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(result == input)]
fn lifetime_return_ref_named_identity<'a>(input: &'a u64) -> &'a u64 {
    input
}

#[trust_vc::requires(value == 12u64)]
#[trust_vc::ensures(true)]
fn lifetime_return_ref_named_identity_caller(value: u64) {
    let borrowed = lifetime_return_ref_named_identity(&value);
    trust_vc::assert!(*borrowed == 12u64);
}

#[trust_vc::requires(*input == 12u64)]
#[trust_vc::ensures(result == 12u64)]
fn lifetime_shared_ref_read_verified(input: &u64) -> u64 {
    *input
}

#[trust_vc::ensures(result.value == input)]
fn lifetime_ref_holder_named_identity_currently_blocked<'a>(
    input: &'a u64,
) -> LifetimeRefHolder<'a> {
    LifetimeRefHolder { value: input }
}

#[trust_vc::requires(value == 12u64)]
#[trust_vc::ensures(true)]
fn lifetime_ref_holder_named_identity_caller_currently_blocked(value: u64) {
    let holder = lifetime_ref_holder_named_identity_currently_blocked(&value);
    trust_vc::assert!(*holder.value == 12u64);
}

#[trust_vc::requires(value == 12u64)]
#[trust_vc::ensures(true)]
fn lifetime_copy_payload_reuse_ok(value: u64) {
    let token = LifetimeCopyToken { value };

    consume_copy_token(token);
    consume_copy_token(token);
    trust_vc::assert!(token.value == 12u64);
}

#[trust_vc::requires(value < 1000u64)]
#[trust_vc::ensures(true)]
fn lifetime_mutable_reference_scalar_write_verified(value: u64) {
    let mut local = value;
    let borrowed: &mut u64 = &mut local;

    *borrowed = value + 1u64;
    trust_vc::assert!(local == value + 1u64);
}

#[trust_vc::ensures(true)]
fn lifetime_mutable_reference_write_currently_blocked() {
    let mut local = 12u64;
    let borrowed: &mut u64 = &mut local;
    let reborrowed: &mut u64 = &mut *borrowed;

    *reborrowed = 13u64;
    trust_vc::assert!(*borrowed == 13u64);
}

// De-surrogated 2026-07-18 (scalar `&mut` deref-write support + compound
// assignment lowering): `*borrowed += 1` through a local mutable reference now
// verifies; discriminator-certified genuine (falsified variant Counterexamples).
#[trust_vc::requires(value < 1000u64)]
#[trust_vc::ensures(true)]
fn lifetime_compound_mutable_reference_assignment_verified(value: u64) {
    let mut local = value;
    let borrowed: &mut u64 = &mut local;

    *borrowed += 1u64;
    trust_vc::assert!(local == value + 1u64);
}

#[trust_vc::ensures(true)]
fn lifetime_false_assert_counterexample() {
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn lifetime_assign_twice_false_tail_counterexample() {
    let mut local = 12u64;

    local = 13u64;
    let _ = local;
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn lifetime_mutable_reference_scalar_write_false_tail_counterexample() {
    let mut local = 12u64;
    let borrowed: &mut u64 = &mut local;

    *borrowed = 13u64;
    trust_vc::assert!(false);
}
