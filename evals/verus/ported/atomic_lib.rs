// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/atomic_lib.rs`.
//
// The upstream file validates Verus `PAtomic*` permission APIs across integer,
// bool, weak/strong compare-exchange, wrapping, bitwise, min/max, and
// target-width usize/isize cases. TrustVc does not currently provide those
// tracked atomic permission types, weak compare-exchange nondeterminism, or a
// direct replacement for Rust/std atomic method contracts.
//
// This scout keeps the manifest entry unsupported-gap and records only
// Rust-valid behavior TrustVc can execute today:
// - a local scalar permission-value surrogate for the load/store/swap flow;
// - bit-vector-backed u32 arithmetic/bitwise operation witnesses;
// - bool fetch_or/fetch_and/fetch_xor/fetch_nand operation witnesses;
// - a false post-store assertion rejected as a counterexample; and
// - direct `std::sync::atomic::AtomicU32` method use as a fail-closed boundary.

#![allow(dead_code)]

use std::sync::atomic::{AtomicU32, Ordering};

pub const ATOMIC_LIB_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "atomic_u32_load_store_swap_verified",
        "test_atomic_u32_pass load/store/swap prefix",
        "verified",
        1,
    ),
    (
        "atomic_u32_wrapping_and_bitwise_surrogate_verified",
        "test_atomic_u32_pass wrapping/bitwise/min/max/exchange prefix",
        "verified",
        1,
    ),
    (
        "atomic_bool_bitwise_surrogate_verified",
        "test_atomic_bool_pass bool bitwise/exchange prefix",
        "verified",
        1,
    ),
    (
        "atomic_u32_store_wrong_value_counterexample",
        "test_atomic_u32_smoke false assertion",
        "counterexample",
        1,
    ),
    (
        "atomic_bool_nand_wrong_value_counterexample",
        "test_atomic_bool_smoke false assertion",
        "counterexample",
        1,
    ),
    (
        "std_atomic_u32_load_currently_blocked",
        "PAtomicU32/std atomic method boundary",
        "error",
        0,
    ),
];

pub fn atomic_lib_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    ATOMIC_LIB_RS_EXPECTED_CASES
}

pub const ATOMIC_LIB_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] =
    &[("std_atomic_u32_load_currently_blocked", &["AtomicU32"])];

pub fn atomic_lib_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    ATOMIC_LIB_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn atomic_u32_load_store_swap_verified() {
    let mut value = 5u32;

    trust_vc::assert!(value == 5u32);

    let loaded = value;
    trust_vc::assert!(loaded == 5u32);

    value = 6u32;
    trust_vc::assert!(value == 6u32);

    let swapped_out = value;
    value = 9u32;
    trust_vc::assert!(swapped_out == 6u32);
    trust_vc::assert!(value == 9u32);
}

#[trust_vc::ensures(true)]
fn atomic_u32_wrapping_and_bitwise_surrogate_verified() {
    let mut value = 9u32;

    let add_old = value;
    trust_vc::assert_by_bit_vector!(9u32.wrapping_add(u32::MAX) == 8u32);
    value = 8u32;
    trust_vc::assert!(add_old == 9u32);
    trust_vc::assert!(value == 8u32);

    let sub_old = value;
    trust_vc::assert_by_bit_vector!(8u32.wrapping_sub(u32::MAX) == 9u32);
    value = 9u32;
    trust_vc::assert!(sub_old == 8u32);
    trust_vc::assert!(value == 9u32);

    let or_old = value;
    trust_vc::assert_by_bit_vector!((9u32 | 2u32) == 11u32);
    value = 11u32;
    trust_vc::assert!(or_old == 9u32);
    trust_vc::assert!(value == 11u32);

    let and_old = value;
    trust_vc::assert_by_bit_vector!((11u32 & 6u32) == 2u32);
    value = 2u32;
    trust_vc::assert!(and_old == 11u32);
    trust_vc::assert!(value == 2u32);

    let xor_old = value;
    trust_vc::assert_by_bit_vector!((2u32 ^ 3u32) == 1u32);
    value = 1u32;
    trust_vc::assert!(xor_old == 2u32);
    trust_vc::assert!(value == 1u32);

    let max_old = value;
    trust_vc::assert!(max_old < 5u32);
    value = 5u32;
    trust_vc::assert!(value == 5u32);

    let min_old = value;
    trust_vc::assert!(min_old > 4u32);
    value = 4u32;
    trust_vc::assert!(value == 4u32);

    let failed_exchange_returned = value;
    let failed_exchange_stored = value;
    let failed_exchange_success = false;
    trust_vc::assert!(failed_exchange_returned == 4u32);
    trust_vc::assert!(failed_exchange_stored == 4u32);
    trust_vc::assert!(!failed_exchange_success);

    let exchange_old = value;
    value = 6u32;
    let successful_exchange_returned = exchange_old;
    let successful_exchange_stored = value;
    let successful_exchange_success = true;
    trust_vc::assert!(successful_exchange_returned == 4u32);
    trust_vc::assert!(successful_exchange_stored == 6u32);
    trust_vc::assert!(successful_exchange_success);

    let nand_old = value;
    trust_vc::assert_by_bit_vector!(!(6u32 & 3u32) == 0xffff_fffdu32);
    value = 0xffff_fffdu32;
    trust_vc::assert!(nand_old == 6u32);
    trust_vc::assert!(value == 0xffff_fffdu32);
}

#[trust_vc::ensures(true)]
fn atomic_bool_bitwise_surrogate_verified() {
    let mut value = false;

    trust_vc::assert!(!value);

    let loaded = value;
    trust_vc::assert!(!loaded);

    value = true;
    trust_vc::assert!(value);

    let swapped_out = value;
    value = false;
    trust_vc::assert!(swapped_out);
    trust_vc::assert!(!value);

    let or_false_old = value;
    value = value || false;
    trust_vc::assert!(!or_false_old);
    trust_vc::assert!(!value);

    let or_true_old = value;
    value = value || true;
    trust_vc::assert!(!or_true_old);
    trust_vc::assert!(value);

    let and_true_old = value;
    value = value && true;
    trust_vc::assert!(and_true_old);
    trust_vc::assert!(value);

    let and_false_old = value;
    value = value && false;
    trust_vc::assert!(and_false_old);
    trust_vc::assert!(!value);

    let xor_false_old = value;
    value = value ^ false;
    trust_vc::assert!(!xor_false_old);
    trust_vc::assert!(!value);

    let xor_true_old = value;
    value = value ^ true;
    trust_vc::assert!(!xor_true_old);
    trust_vc::assert!(value);

    let nand_false_old = value;
    value = !(value && false);
    trust_vc::assert!(nand_false_old);
    trust_vc::assert!(value);

    let nand_true_old = value;
    value = !(value && true);
    trust_vc::assert!(nand_true_old);
    trust_vc::assert!(!value);

    let failed_exchange_returned = value;
    let failed_exchange_stored = value;
    let failed_exchange_success = false;
    trust_vc::assert!(!failed_exchange_returned);
    trust_vc::assert!(!failed_exchange_stored);
    trust_vc::assert!(!failed_exchange_success);

    let exchange_old = value;
    value = true;
    let successful_exchange_returned = exchange_old;
    let successful_exchange_stored = value;
    let successful_exchange_success = true;
    trust_vc::assert!(!successful_exchange_returned);
    trust_vc::assert!(successful_exchange_stored);
    trust_vc::assert!(successful_exchange_success);
}

#[trust_vc::ensures(true)]
fn atomic_u32_store_wrong_value_counterexample() {
    let mut value = 5u32;

    value = 6u32;

    trust_vc::assert!(value == 5u32);
}

#[trust_vc::ensures(true)]
fn atomic_bool_nand_wrong_value_counterexample() {
    let mut value = true;

    value = !(value && true);

    trust_vc::assert!(value);
}

#[trust_vc::ensures(true)]
fn std_atomic_u32_load_currently_blocked() {
    let atomic = AtomicU32::new(5u32);
    let loaded = atomic.load(Ordering::SeqCst);

    trust_vc::assert!(loaded == 5u32);
}
