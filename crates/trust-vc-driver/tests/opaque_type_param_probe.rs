// PROBE: does the encoder/ay accept an opaque (uninterpreted) type-parameter
// sort and reason over it with EUF equality only?
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// This runs on the STABLE seam (no rustc-driver feature): it builds `DriverFn`s
// whose bindings carry `TrustVcType::TypeParam(_)` (the opaque sort the driver's
// `map_opaque_type_param` will emit) and runs them through the REAL encoder + ay.
// It establishes, by construction, that:
//   (1) a variable of the opaque sort can be declared and equated (reflexive
//       equality VERIFIES) — the encoder accepts `Sort::Uninterpreted("Poly")`;
//   (2) equality is a genuine congruence, NOT everything-equal: two independent
//       opaque values are NOT forced equal, so a claim that they are is REFUTED
//       (the uninterpreted sort admits >= 2 elements — no singleton collapse);
//   (3) a datatype carrying an opaque field roundtrips through
//       constructor/selector (the native datatype theory carries Poly fields).
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use trust_vc_core::ir::{CompareOp, DatatypeVariant, TrustVcExpr, TrustVcType};
use trust_vc_driver::lower::{Binding, DriverFn, Outcome};

fn tp() -> TrustVcType {
    TrustVcType::TypeParam("T".to_string())
}

fn eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

/// (1) `fn id<T>(x: T) -> T ensures result == x { x }` — reflexive opaque
/// equality VERIFIES. Confirms the encoder accepts a var of the opaque sort.
#[test]
fn opaque_reflexive_equality_verifies() {
    let f = DriverFn {
        name: "id".into(),
        params: vec![Binding::new("x", tp())],
        result: Binding::new("result", tp()),
        requires: vec![],
        body_value: Some(var("x", tp())),
        ensures: vec![eq(var("result", tp()), var("x", tp()))],
    };
    let (outcome, raw) = f.verify_exec();
    assert_eq!(outcome, Outcome::Verified, "raw: {raw:?}");
}

/// (2) `fn pick<T>(x: T, y: T) -> T ensures result == y { x }` — the opaque sort
/// is NOT everything-equal, so `result(==x) == y` is REFUTED (a 2-element model
/// exists). This is the load-bearing soundness fact: if the sort collapsed to a
/// singleton, this would wrongly VERIFY (a false-Verify for-all-T).
#[test]
fn opaque_distinct_values_not_forced_equal_refuted() {
    let f = DriverFn {
        name: "pick".into(),
        params: vec![Binding::new("x", tp()), Binding::new("y", tp())],
        result: Binding::new("result", tp()),
        requires: vec![],
        body_value: Some(var("x", tp())),
        ensures: vec![eq(var("result", tp()), var("y", tp()))],
    };
    let (outcome, raw) = f.verify_exec();
    assert_eq!(outcome, Outcome::Refuted, "raw: {raw:?}");
}

/// (3) A single-variant datatype with an opaque field roundtrips through
/// constructor+selector: `S{f:T}`, `get(S{f:x}).f == x` VERIFIES; reading a
/// second opaque field `g` after building with `f:x, g:y` is NOT forced to `x`
/// (REFUTED). Confirms the native datatype theory carries Poly-sorted fields.
fn s_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "S".to_string(),
        variants: vec![DatatypeVariant::new(
            "S",
            vec![("f".to_string(), tp()), ("g".to_string(), tp())],
        )],
    }
}

fn ctor(x: TrustVcExpr, y: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "S_S".to_string(),
        args: vec![x, y],
        return_ty: s_ty(),
    }
}

fn sel(field: &str, recv: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: format!("S_S_{field}"),
        args: vec![recv],
        return_ty: tp(),
    }
}

#[test]
fn opaque_datatype_field_roundtrip_verifies() {
    // result == (S{f:x, g:y}).f ; ensures result == x  → Verified.
    let f = DriverFn {
        name: "get_f".into(),
        params: vec![Binding::new("x", tp()), Binding::new("y", tp())],
        result: Binding::new("result", tp()),
        requires: vec![],
        body_value: Some(sel("f", ctor(var("x", tp()), var("y", tp())))),
        ensures: vec![eq(var("result", tp()), var("x", tp()))],
    };
    let (outcome, raw) = f.verify_exec();
    assert_eq!(outcome, Outcome::Verified, "roundtrip: {raw:?}");
}

#[test]
fn opaque_datatype_wrong_field_refuted() {
    // result == (S{f:x, g:y}).g ; ensures result == x  → Refuted (g is y, not x).
    let f = DriverFn {
        name: "get_g".into(),
        params: vec![Binding::new("x", tp()), Binding::new("y", tp())],
        result: Binding::new("result", tp()),
        requires: vec![],
        body_value: Some(sel("g", ctor(var("x", tp()), var("y", tp())))),
        ensures: vec![eq(var("result", tp()), var("x", tp()))],
    };
    let (outcome, raw) = f.verify_exec();
    assert_eq!(outcome, Outcome::Refuted, "wrong-field: {raw:?}");
}
