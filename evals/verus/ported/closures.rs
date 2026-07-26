// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/closures.rs`.
//
// This file intentionally covers only a Rust-valid closure slice: typed
// `SpecFn::new` closure literals that TrustVc can compare extensionally, direct
// unary `SpecFn::call`, typed closures that capture surrounding proof values,
// and a concrete helper accepting a `SpecFn` argument. It also keeps direct
// local closures, closure-parameter inference, and return-in-closure surfaces
// fail-closed. Full upstream parity still requires direct proof-local closure
// calls, broader closure inference, higher-order `spec_fn` parameter
// application/refinement, polymorphic closures, and exact diagnostic parity.

#![allow(dead_code)]

use trust_vc_types::{int, SpecFn};

pub type ClosuresRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ClosuresRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CLOSURES_RS_EXPECTED_CASES: &[ClosuresRsExpectedCase] = &[
    (
        "spec_fn_closure_add_one_extensional",
        "test1",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_add_one_wrong_counterexample",
        "test1_fails4",
        "counterexample",
        1,
    ),
    (
        "spec_fn_two_arg_bool_extensional",
        "test1",
        "verified",
        1,
    ),
    (
        "spec_fn_two_arg_bool_wrong_counterexample",
        "test1_fails1",
        "counterexample",
        1,
    ),
    (
        "spec_fn_tuple_binder_extensional",
        "",
        "verified",
        1,
    ),
    (
        "spec_fn_tuple_binder_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "spec_fn_closure_capture_arithmetic_extensional",
        "",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_capture_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "spec_fn_value_call_reflexive_verified",
        "",
        "verified",
        1,
    ),
    (
        "spec_fn_value_call_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "spec_fn_direct_call_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "spec_fn_argument_apply_to_one_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "local_closure_application_currently_errors",
        "test1",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_parameter_inference_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "return_in_spec_fn_closure_currently_errors",
        "return_in_closure",
        "error",
        0,
    ),
];

pub const CLOSURES_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ClosuresRsFailClosedErrorPatterns] = &[
    (
        "spec_fn_direct_call_currently_errors",
        &[
            "SpecFn::new(...) closures cannot be encoded directly",
            "higher-order combinator",
        ],
    ),
    (
        "spec_fn_argument_apply_to_one_currently_errors",
        &[
            "SpecFn::new(...) closures cannot be encoded directly",
            "higher-order combinator",
        ],
    ),
    (
        "spec_fn_closure_parameter_inference_currently_errors",
        &[
            "requires an explicit type annotation",
            "spec closure parameter",
        ],
    ),
    (
        "return_in_spec_fn_closure_currently_errors",
        &[
            "return",
            "block expression",
            "unsupported expression",
            "SpecFn::new(...) closures cannot be encoded directly",
        ],
    ),
];

pub fn closures_rs_expected_cases() -> &'static [ClosuresRsExpectedCase] {
    CLOSURES_RS_EXPECTED_CASES
}

pub fn closures_rs_fail_closed_error_patterns() -> &'static [ClosuresRsFailClosedErrorPatterns] {
    CLOSURES_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(result == f.call(x))]
fn apply_spec_fn_to_int(f: SpecFn<int, int>, x: int) -> int {
    f.call(x)
}

#[trust_vc::ensures(true)]
fn spec_fn_closure_add_one_extensional() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|x: int| x + 1),
        SpecFn::new(|y: int| 1 + y)
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_closure_add_one_wrong_counterexample() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|x: int| x + 1),
        SpecFn::new(|y: int| y + 2)
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_two_arg_bool_extensional() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|x: u32, y: u64| (x as u64) < y),
        SpecFn::new(|a: u32, b: u64| b > (a as u64))
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_two_arg_bool_wrong_counterexample() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|x: u32, y: u64| (x as u64) < y),
        SpecFn::new(|a: u32, b: u64| b >= (a as u64))
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_tuple_binder_extensional() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|(i, x): (int, int)| x + i),
        SpecFn::new(|(j, y): (int, int)| j + y)
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_tuple_binder_wrong_counterexample() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|(i, x): (int, int)| x + i),
        SpecFn::new(|(j, y): (int, int)| j + y + 1)
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_closure_capture_arithmetic_extensional(p: int, q: int) {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|z: int| ((z + 1) + p) + q),
        SpecFn::new(|z: int| z + ((p + q) + 1))
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_closure_capture_wrong_counterexample(p: int, q: int) {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|z: int| ((z + 1) + p) + q),
        SpecFn::new(|z: int| z + ((p + q) + 2))
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_value_call_reflexive_verified(f: SpecFn<int, int>, n: int) {
    trust_vc::assert!(f.call(n) == f.call(n));
}

#[trust_vc::ensures(true)]
fn spec_fn_value_call_wrong_counterexample(f: SpecFn<int, int>, n: int) {
    trust_vc::assert!(f.call(n) == f.call(n + 1));
}

#[trust_vc::ensures(true)]
fn spec_fn_direct_call_currently_errors() {
    let f: SpecFn<int, int> = SpecFn::new(|x: int| x + 1);
    trust_vc::assert!(f.call(10) == 11);
}

#[trust_vc::ensures(true)]
fn spec_fn_argument_apply_to_one_currently_errors() {
    let y = apply_spec_fn_to_int(SpecFn::new(|x: int| x + 1), 5);
    trust_vc::assert!(y == 6);
}

// FLIP (bare-closure inline): a bare (non-`closure!`) capture-free local closure
// applied by name is now INLINED at the call site — `f(10)` models as its body
// `10 + 1`, so the true assertion `f(10) == 11` VERIFIES (formerly fail-closed
// "unknown return type for function 'f'"). Historical `_currently_errors` case-id
// retained for stable upstream/manifest mapping, per the exec_closures convention.
#[trust_vc::ensures(true)]
fn local_closure_application_currently_errors() {
    let f = |x: int| x + 1;
    trust_vc::assert!(f(10) == 11);
}

#[trust_vc::ensures(true)]
fn spec_fn_closure_parameter_inference_currently_errors() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|z| z + 1),
        SpecFn::new(|z: int| z + 1)
    ));
}

#[trust_vc::ensures(true)]
fn return_in_spec_fn_closure_currently_errors() {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|x: int| -> int {
            return x;
        }),
        SpecFn::new(|x: int| x)
    ));
}
