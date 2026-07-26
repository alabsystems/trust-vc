// End-to-end tests for the trust-vc-driver lowering seam.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// These tests build a fully-typed `DriverFn` (the shape the rustc-driver THIR
// walker will produce) and run it through trust-vc-core's REAL encoder + ay
// solver. They prove three things the design depends on:
//   1. typed front-end input drives the existing backend with no syn,
//   2. valid postconditions VERIFY, and
//   3. false postconditions are REFUTED with a counterexample (the seam is
//      sound, not a rubber stamp).
//
// This is the load-bearing, stable-toolchain demonstration of the
// rustc-driver-frontend architecture (see design-rustc-driver-frontend.md).
//
// When the `rustc-driver` feature is on, linking the feature-on lib pulls in
// `rustc_driver`, so this binary must opt into `rustc_private` to link it (a
// no-op in the default stable build, which keeps `lower_end_to_end` portable).
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use trust_vc_core::ir::CompareOp;
use trust_vc_driver::lower::{add, cmp, lit, mul, uint, var, Binding, DriverFn, Outcome};

fn u32t() -> trust_vc_core::ir::TrustVcType {
    uint(32)
}

/// fn add_bounds(x: u32, y: u32) -> u32
///     requires x < 100, y < 100
///     ensures result < 200, result >= x
/// { x + y }
#[test]
fn valid_postcondition_verifies() {
    let f = DriverFn {
        name: "add_bounds".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![
            cmp(CompareOp::Lt, var("result", u32t()), lit(200, u32t())),
            cmp(CompareOp::Ge, var("result", u32t()), var("x", u32t())),
        ],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// Same function, but a FALSE postcondition `result < 150` (x=99,y=99 → 198).
/// The backend must refute it with a counterexample — not rubber-stamp it.
#[test]
fn false_postcondition_is_refuted() {
    let f = DriverFn {
        name: "add_bounds_false".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(150, u32t()))],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// fn square(x: u32) -> u32 requires x <= 10 ensures result <= 100, result >= x
/// { x * x }  — exercises multiplication and multiple postconditions.
#[test]
fn multiplication_with_multiple_postconditions_verifies() {
    let f = DriverFn {
        name: "square".into(),
        params: vec![Binding::new("x", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![cmp(CompareOp::Le, var("x", u32t()), lit(10, u32t()))],
        body_value: Some(mul(var("x", u32t()), var("x", u32t()), u32t())),
        ensures: vec![
            cmp(CompareOp::Le, var("result", u32t()), lit(100, u32t())),
            cmp(CompareOp::Ge, var("result", u32t()), var("x", u32t())),
        ],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// Tightening the bound to a FALSE `result < 100` (x=10 → 100) must be refuted —
/// confirms the multiplication path is checked, not assumed.
#[test]
fn multiplication_false_bound_is_refuted() {
    let f = DriverFn {
        name: "square_false".into(),
        params: vec![Binding::new("x", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![cmp(CompareOp::Le, var("x", u32t()), lit(10, u32t()))],
        body_value: Some(mul(var("x", u32t()), var("x", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(100, u32t()))],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// Soundness foundation for "strictly superior to Verus": a FALSE overflow claim
/// must be REFUTED. `wrapping_add(a, 1) > a` is false for `a == u64::MAX` (the
/// sum wraps to 0). This is exactly the property the `overflow.rs` port guarded
/// away with `assume!(a < 30)`; here the unguarded claim is correctly refuted
/// with a counterexample. Soundness — not the verdict-matching the guarded port
/// faked — is what makes trust-vc a candidate to be *strictly superior* to Verus.
#[test]
fn unsigned_overflow_wrap_is_refuted() {
    use trust_vc_core::ir::{ArithOp, TrustVcExpr, WrappingMode};
    let u64t = uint(64);
    // result == a.wrapping_add(1)  (BV modular add, no overflow side-check)
    let body = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Wrapping,
        op: ArithOp::Add,
        left: Box::new(var("a", u64t.clone())),
        right: Box::new(lit(1, u64t.clone())),
        ty: u64t.clone(),
    };
    let f = DriverFn {
        name: "succ_gt".into(),
        params: vec![Binding::new("a", u64t.clone())],
        result: Binding::new("result", u64t.clone()),
        requires: vec![],
        body_value: Some(body),
        ensures: vec![cmp(
            CompareOp::Gt,
            var("result", u64t.clone()),
            var("a", u64t),
        )],
    };
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}
