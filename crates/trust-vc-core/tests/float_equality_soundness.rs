// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Float equality is IEEE equality, which is not reflexive.
//!
//! Rust compares an `f64` or `f32` with IEEE `==`: `NaN == NaN` is false and
//! `0.0 == -0.0` is true. A derived `PartialEq`, a tuple, `Option`, `Vec` and
//! `Vec::contains` compare a float component the same way. The lane read `==`
//! on such a compound value as structural equality, which always holds for a
//! value and itself, so `p == p` over `struct P { f: f64 }` was `Verified`.
//! Separately, the concrete evaluator that closes a solver `unknown` decided
//! `a == a` by reflexivity for any pure operand, a float included, so
//! `p.f == p.f`, and `x == x` in a file whose axioms made the solver answer
//! `unknown`, were `Verified` too.
//!
//! Every liar below was `Verified` before the fix and panics when compiled with
//! `trustc` and called with a NaN (`m24` panics without one; it was `unknown`).
//! A compound comparison that holds a float, and `contains` over float
//! elements, now fail closed; a `Vec` whose elements have a hand-written
//! `PartialEq` is refused the same way. A float compared with itself is no
//! longer decided by reflexivity. The true twins, which compare integers,
//! still verify, and a bare float refutation is kept.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_float_equality_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program comparing a compound value that holds a float.
    RefusedFloatCompound,
    /// A false program that writes an unsuffixed float literal into a
    /// struct field (design-trust-proof-backend.md §5b rule 14): refused
    /// there, before its comparison is reached.
    RefusedUnsuffixedFloatField,
    /// A false program using `contains` over elements whose `==` is not
    /// structural.
    RefusedContains,
    /// A false program comparing a `Vec` of a type with a hand-written
    /// `PartialEq`.
    RefusedManualElement,
    /// A false program comparing a float with itself: must not verify, and is
    /// not an error.
    NotVerified,
    /// A false program the lane refutes: the refutation must be kept.
    Refuted,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(300).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn error_contains(r: &Result<VerifyResult, String>, needle: &str) -> bool {
    matches!(r, Ok(VerifyResult::Error { message }) if message.contains(needle))
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::RefusedFloatCompound => {
                error_contains(&r, "compares a float inside a compound value")
            }
            Expect::RefusedUnsuffixedFloatField => {
                error_contains(&r, "is an unsuffixed float literal held by a struct field")
            }
            Expect::RefusedContains => error_contains(&r, "is not structural membership"),
            Expect::RefusedManualElement => error_contains(&r, "hand-written `PartialEq`"),
            Expect::NotVerified => matches!(
                r,
                Ok(VerifyResult::NotProved { .. }
                    | VerifyResult::Unknown { .. }
                    | VerifyResult::Counterexample { .. })
            ),
            Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{
    NotVerified, RefusedContains, RefusedFloatCompound, RefusedManualElement,
    RefusedUnsuffixedFloatField, Refuted, Verified,
};

const DERIVED_SRC: &str = r#"
#![allow(dead_code, unused)]

#[derive(PartialEq)]
struct P {
    f: f64,
}

#[derive(PartialEq, Clone, Copy, Debug)]
struct Q {
    f: f64,
}

#[derive(PartialEq)]
struct O {
    p: P,
    n: u8,
}

#[derive(PartialEq)]
enum E {
    A(f64),
    B,
}

#[derive(PartialEq)]
struct F32 {
    f: f32,
}

struct R {
    f: f64,
    n: u64,
}

#[derive(PartialEq)]
struct Pi {
    x: u64,
}

#[derive(PartialEq, Clone, Copy)]
struct Pn {
    x: u64,
    b: bool,
}

#[trust_vc::ensures(true)]
fn m18(p: P) {
    assert!(p == p);
}

#[trust_vc::requires(p == q)]
#[trust_vc::ensures(true)]
fn m19(p: Q, q: Q) {
    assert!(p == q);
}

#[trust_vc::ensures(true)]
fn m20(p: P) {
    assert!(!(p != p));
}

#[trust_vc::ensures(true)]
fn m21(o: O) {
    assert!(o == o);
}

#[trust_vc::ensures(true)]
fn m22(e: E) {
    assert!(e == e);
}

#[trust_vc::ensures(true)]
fn m23(p: F32) {
    assert!(p == p);
}

#[trust_vc::ensures(true)]
fn m24() {
    let p = P { f: 0.0 };
    let q = P { f: -0.0 };
    assert!(p != q);
}

#[trust_vc::ensures(true)]
fn m24b() {
    let p = P { f: 0.0f64 };
    let q = P { f: -0.0f64 };
    assert!(p != q);
}

#[trust_vc::ensures(true)]
fn m25(x: f64) {
    let t = (x, 1u8);
    assert!(t == t);
}

#[trust_vc::ensures(true)]
fn m26(x: f64) {
    let o = Some(x);
    assert!(o == o);
}

#[trust_vc::ensures(true)]
fn m28(p: Q) -> bool {
    let b = p == p;
    assert!(b);
    b
}

#[trust_vc::ensures(result)]
fn m29(p: Q) -> bool {
    p == p
}

#[trust_vc::ensures(true)]
fn m30(p: Q) {
    if p == p {
    } else {
        assert!(false);
    }
}

#[trust_vc::ensures(true)]
fn m31(x: f64) {
    let v = vec![x];
    assert!(v == v);
}

#[trust_vc::ensures(true)]
fn m33(p: Q) {
    assert_eq!(p, p);
}

#[trust_vc::ensures(true)]
fn m34(x: f64) {
    let t = (x,);
    let u = t;
    assert!(t == u);
}

#[trust_vc::ensures(true)]
fn n5(p: Q) {
    let q = p;
    assert!(p == q);
}

#[trust_vc::ensures(true)]
fn n7(x: f64) {
    let o: Option<f64> = Some(x);
    assert!(o == Some(x));
}

#[trust_vc::ensures(true)]
fn n9(x: f64, y: u64) {
    assert!((x, y) == (x, y));
}

#[trust_vc::ensures(true)]
fn n1(x: f64) {
    let v = vec![x];
    assert!(v.contains(&x));
}

#[trust_vc::ensures(true)]
fn n13(p: Q) {
    let v = vec![p];
    assert!(v.contains(&p));
}

#[trust_vc::ensures(true)]
fn x2(p: Q) {
    assert!(p.f == p.f);
}

#[trust_vc::ensures(true)]
fn x3(p: Q) {
    let f = p.f;
    assert!(f == f);
}

#[trust_vc::ensures(true)]
fn x5(p: Q) {
    assert!(!(p.f != p.f));
}

#[trust_vc::ensures(true)]
fn x6(p: R) {
    assert!(p.f == p.f);
}

#[trust_vc::ensures(true)]
fn x9(p: R) {
    assert!(p.f == p.f || p.n == 0u64);
}

#[trust_vc::ensures(true)]
fn t1(p: Pi) {
    assert!(p == p);
}

#[trust_vc::ensures(true)]
fn t2(x: u64) {
    let v = vec![x];
    assert!(v == v && v.contains(&x));
}

#[trust_vc::ensures(true)]
fn t3(x: u64, y: bool) {
    let o = Some(x);
    assert!(o == Some(x) && (x, y) == (x, y));
}

#[trust_vc::requires(p == q)]
#[trust_vc::ensures(true)]
fn t4(p: Pn, q: Pn) {
    assert!(p == q);
}

#[trust_vc::ensures(true)]
fn t5(p: Q) {
    let f = p.f;
    assert!(f == p.f || f != f);
}

#[trust_vc::ensures(true)]
fn x1(x: f64) {
    assert!(x == x);
}
"#;

/// `==` on a compound value holding a float, and `contains` over float
/// elements, fail closed; a float field compared with itself is not decided by
/// reflexivity. Integer compounds still verify, and a bare float `x == x` is
/// still refuted with `x = NaN`.
#[test]
fn a_compound_holding_a_float_is_not_compared_structurally() {
    check_table(
        DERIVED_SRC,
        &[
            ("m18", RefusedFloatCompound),
            ("m19", RefusedFloatCompound),
            ("m20", RefusedFloatCompound),
            ("m21", RefusedFloatCompound),
            ("m22", RefusedFloatCompound),
            ("m23", RefusedFloatCompound),
            ("m24", RefusedUnsuffixedFloatField),
            ("m24b", RefusedFloatCompound),
            ("m25", RefusedFloatCompound),
            ("m26", RefusedFloatCompound),
            ("m28", RefusedFloatCompound),
            ("m29", RefusedFloatCompound),
            ("m30", RefusedFloatCompound),
            ("m31", RefusedFloatCompound),
            ("m33", RefusedFloatCompound),
            ("m34", RefusedFloatCompound),
            ("n5", RefusedFloatCompound),
            ("n7", RefusedFloatCompound),
            ("n9", RefusedFloatCompound),
            ("n1", RefusedContains),
            ("n13", RefusedContains),
            ("x2", NotVerified),
            ("x3", NotVerified),
            ("x5", NotVerified),
            ("x6", NotVerified),
            ("x9", NotVerified),
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("t5", Verified),
            ("x1", Refuted),
        ],
    );
}

/// A hand-written `PartialEq` publishes a quantified body axiom, under which
/// the solver answers `unknown` for `x == x`; the evaluator that closes an
/// `unknown` used to decide it by reflexivity. `Vec` equality and `contains`
/// call the elements' hand-written `eq`, so they are refused.
const MANUAL_SRC: &str = r#"
#![allow(dead_code, unused)]

struct M(u64);

impl PartialEq for M {
    fn eq(&self, _o: &M) -> bool {
        false
    }
}

#[trust_vc::ensures(true)]
fn n2() {
    let v = vec![M(1)];
    assert!(v == v);
}

#[trust_vc::ensures(true)]
fn n14() {
    let v = vec![M(1)];
    assert!(v.contains(&M(1)));
}

#[trust_vc::ensures(true)]
fn i1(x: f64) {
    assert!(x == x);
}

#[trust_vc::ensures(result == false)]
fn i2(x: f64) -> bool {
    x != x
}

#[trust_vc::ensures(true)]
fn t6(x: u64) {
    assert!(x == x);
}
"#;

#[test]
fn a_float_is_not_equal_to_itself_by_reflexivity() {
    check_table(
        MANUAL_SRC,
        &[
            ("n2", RefusedManualElement),
            ("n14", RefusedContains),
            ("i1", NotVerified),
            ("i2", NotVerified),
            ("t6", Verified),
        ],
    );
}
