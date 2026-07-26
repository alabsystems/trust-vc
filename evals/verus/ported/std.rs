// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! First partial executable TrustVc scout for upstream Verus
//! `source/rust_verify_test/tests/std.rs`.
//!
//! This file is intentionally not full replacement evidence for upstream
//! std.rs. It covers only stable Rust-valid behavior currently expressible in
//! TrustVc: selected std runtime clone/allocation/control-flow operations,
//! upstream-shaped wrapping multiplication proofs and counterexamples, one
//! Vec macro/view/index prefix, and fail-closed boundaries for broader std
//! library surfaces that still need one-to-one support.

#![allow(
    clippy::clone_on_copy,
    clippy::eq_op,
    clippy::len_zero,
    clippy::ptr_arg,
    clippy::useless_vec,
    dead_code,
    noop_method_call,
    unused_imports,
    unused_variables
)]

use trust_vc_types::View;

pub const STD_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "unsigned_wrapping_mul_constants_verified",
        "unsigned_wrapping_mul",
        "verified",
        3,
    ),
    (
        "signed_wrapping_mul_prefix_constants_verified",
        "signed_wrapping_mul",
        "verified",
        5,
    ),
    (
        "unsigned_wrapping_mul_wrong_value_counterexample",
        "unsigned_wrapping_mul",
        "counterexample",
        1,
    ),
    (
        "signed_wrapping_mul_false_tail_counterexample",
        "signed_wrapping_mul",
        "counterexample",
        1,
    ),
    (
        "vec_macro_literal_view_verified",
        "vec_macro",
        "verified",
        4,
    ),
    (
        "index_vec_in_bounds_copy_verified",
        "index_vec_in_bounds",
        "verified",
        1,
    ),
    ("box_new_deref_currently_blocked", "box_new", "error", 0),
    ("rc_arc_clone_deref_currently_blocked", "rc_arc", "error", 0),
];

pub const STD_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "box_new_deref_currently_blocked",
        &["Box", "deref", "unsupported"],
    ),
    (
        "rc_arc_clone_deref_currently_blocked",
        &["unresolved variable", "Rc", "Arc"],
    ),
];

pub fn std_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    STD_RS_EXPECTED_CASES
}

pub fn std_rs_fail_closed_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    STD_RS_FAIL_CLOSED_ERROR_PATTERNS
}

pub fn rc_arc_runtime_clone_deref() {
    use std::rc::Rc;
    use std::sync::Arc;

    let x = Rc::new(5u64);
    assert_eq!(*x, 5u64);
    let x1 = x.clone();
    assert_eq!(*x1, 5u64);

    let y = Arc::new(5u64);
    assert_eq!(*y, 5u64);
    let y1 = y.clone();
    assert_eq!(*y1, 5u64);
}

pub fn ref_clone_runtime_alias() {
    struct X {}

    fn test2(_x: &X) {}

    fn test(x: &X) {
        let y = x.clone();
        assert!(std::ptr::eq(x, y));
        test2(y);
    }

    let value = X {};
    test(&value);
}

pub fn box_new_runtime_deref() {
    let x: Box<u32> = Box::new(5u32);
    assert_eq!(*x, 5u32);
}

pub fn vec_macro_runtime_literal() {
    let v = vec![7u8, 8u8, 9u8];
    assert_eq!(v.len(), 3usize);
    assert_eq!(v[0usize], 7u8);
    assert_eq!(v[1usize], 8u8);
    assert_eq!(v[2usize], 9u8);
}

pub fn question_mark_option_runtime_none_short_circuits() -> Option<u32> {
    let x: Option<u8> = None;
    let _y = x?;

    panic!("None should short-circuit before this point");
}

pub fn question_mark_result_runtime_err_short_circuits() -> Result<u32, bool> {
    let x: Result<u8, bool> = Err(false);
    let _y = x?;

    panic!("Err should short-circuit before this point");
}

pub fn manually_drop_runtime_clone_into_inner() {
    use std::mem::ManuallyDrop;

    let x = ManuallyDrop::new(20u64);
    assert_eq!(*x, 20u64);
    let x1 = x.clone();
    assert_eq!(*x1, 20u64);
    let y = ManuallyDrop::into_inner(x);
    assert_eq!(y, 20u64);
}

fn unsigned_wrapping_mul_constants_verified() {
    trust_vc::assert_by_bit_vector!(255u16.wrapping_mul(253u16) == 64515u16);
    trust_vc::assert_by_bit_vector!(256u16.wrapping_mul(256u16) == 0u16);
    trust_vc::assert_by_bit_vector!(257u16.wrapping_mul(259u16) == 1027u16);
}

fn signed_wrapping_mul_prefix_constants_verified() {
    trust_vc::assert_by_bit_vector!((1000i64).wrapping_mul(2000i64) == 2_000_000i64);
    trust_vc::assert_by_bit_vector!((1000i64).wrapping_mul(-2000i64) == -2_000_000i64);
    trust_vc::assert_by_bit_vector!(
        (12_345_678_901i64).wrapping_mul(45_678_912_301i64) == -7_911_882_469_911_038_895i64
    );
    trust_vc::assert_by_bit_vector!(
        (92_345_678_901i64).wrapping_mul(175_678_912_301i64) == 8_500_384_234_389_190_737i64
    );
    trust_vc::assert_by_bit_vector!((12i64).wrapping_mul(2_305_843_009_213_693_952i64) == i64::MIN);
}

fn unsigned_wrapping_mul_wrong_value_counterexample() {
    trust_vc::assert_by_bit_vector!(257u16.wrapping_mul(259u16) == 1028u16);
}

fn signed_wrapping_mul_false_tail_counterexample() {
    trust_vc::assert!(false);
}

fn vec_macro_literal_view_verified() {
    let v = vec![7u8, 8u8, 9u8];

    trust_vc::assert!(v.view().len() == 3usize);
    trust_vc::assert!(v.view().index(0usize) == 7u8);
    trust_vc::assert!(v.view().index(1usize) == 8u8);
    trust_vc::assert!(v.view().index(2usize) == 9u8);
}

fn index_vec_in_bounds_copy_verified(v: &Vec<u8>) {
    trust_vc::assume!(v.len() > 0usize);
    let a = v[0usize] < v[0usize];

    trust_vc::assert!(a == false);
}

fn box_new_deref_currently_blocked() {
    let x: Box<u32> = Box::new(5u32);

    trust_vc::assert!(*x == 5u32);
}

fn rc_arc_clone_deref_currently_blocked() {
    use std::rc::Rc;
    use std::sync::Arc;

    let x = Rc::new(5u64);
    let x1 = x.clone();
    trust_vc::assert!(*x == 5u64);
    trust_vc::assert!(*x1 == 5u64);

    let y = Arc::new(5u64);
    let y1 = y.clone();
    trust_vc::assert!(*y == 5u64);
    trust_vc::assert!(*y1 == 5u64);
}
