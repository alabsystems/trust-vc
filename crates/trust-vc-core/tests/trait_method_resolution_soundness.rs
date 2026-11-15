// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rust resolves `recv.m(..)` by trying the receiver by value, then `&`, then
//! `&mut` at each autoderef step, and the first method that applies wins. A
//! trait method in scope can therefore replace the std or inherent method
//! this lane reads: `impl MyClone for u64 { fn clone(self) -> Self { 7 } }`
//! makes `x.clone()` return 7. A function that reaches a method call whose
//! name such a trait may take gets no `Verified` answer
//! (`vc_extraction::trait_method_resolution`).
//!
//! Every liar below was `Verified` before the rule and is false at run time
//! (compiled with `trustc`, verification off): `h1(3)` and `w1(3)` return 7,
//! `r1(3)` returns 3 against a contract that means `MyClone::clone(x)`, 7;
//! `h2` does the same with the trait in another crate; `b1(vec![])` returns
//! 7; `p1` and `e1` panic; `f1` returns 9, `e2` returns `false`, `c2` returns
//! 7 and `i2` returns 0; and `Get::get` for `S` returns 7 against its
//! `ensures(result == 3)`. Each twin changes the trait's method name, its
//! receiver or the import, verified before the rule, and must still verify.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the rule starts with.
const TAG: &str = "trait method resolution";

fn fixture_path(src: &str, name: &str) -> std::path::PathBuf {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_trait_method_resolution_{}_{}_{seq}.rs",
        std::process::id(),
        name.replace(|c: char| !c.is_ascii_alphanumeric(), "_")
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let path = fixture_path(src, func);
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

fn conformance(src: &str, obligation: &str) -> Result<VerifyResult, String> {
    let path = fixture_path(src, obligation);
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_trait_conformance_obligation(path.to_str().expect("utf8 path"), obligation)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// Refused by the rule: an `Error` carrying its tag.
    Refused,
}

use Expect::{Refused, Verified};

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn matches_expect(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match expect {
        Verified => matches!(r, Ok(VerifyResult::Verified)),
        Refused => matches!(r, Ok(VerifyResult::Error { message }) if message.starts_with(TAG)),
    }
}

/// `(source, function or conformance obligation, expected)`.
type Row = (&'static str, &'static str, Expect);

fn check_rows(rows: &[Row]) {
    let mut failures = Vec::new();
    for (src, name, expect) in rows {
        let r = if name.starts_with("trait impl conformance ") {
            conformance(src, name)
        } else {
            verify(src, name)
        };
        let ok = matches_expect(&r, *expect);
        println!(
            "{name}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{name}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The backlog program, a caller and a contract that reads the call.
const SRC_BACKLOG: &str = r#"
#![allow(dead_code, unused)]
trait MyClone {
    fn clone(self) -> Self;
}
impl MyClone for u64 {
    fn clone(self) -> Self {
        7
    }
}

#[trust_vc::ensures(result == x)]
fn h1(x: u64) -> u64 {
    x.clone()
}

#[trust_vc::ensures(result == x)]
fn w1(x: u64) -> u64 {
    h1(x)
}

#[trust_vc::ensures(result == x.clone())]
fn r1(x: u64) -> u64 {
    x
}
"#;

/// The backlog program with the trait's method renamed: `x.clone()` is the
/// std `Clone::clone`.
const SRC_BACKLOG_TWIN: &str = r#"
#![allow(dead_code, unused)]
trait MyClone {
    fn my_clone(self) -> Self;
}
impl MyClone for u64 {
    fn my_clone(self) -> Self {
        7
    }
}

#[trust_vc::ensures(result == x)]
fn h1(x: u64) -> u64 {
    x.clone()
}
"#;

/// The trait comes from another crate.
const SRC_IMPORTED: &str = r#"
#![allow(dead_code, unused)]
use other::MyClone;

#[trust_vc::ensures(result == x)]
fn h2(x: u64) -> u64 {
    x.clone()
}
"#;

/// The import is of std's own `Clone`.
const SRC_IMPORTED_TWIN: &str = r#"
#![allow(dead_code, unused)]
use std::clone::Clone;

#[trust_vc::ensures(result == x)]
fn h2(x: u64) -> u64 {
    x.clone()
}
"#;

/// A blanket impl hides `Vec::len(&self)`.
const SRC_BLANKET: &str = r#"
#![allow(dead_code, unused)]
trait Len {
    fn len(self) -> usize;
}
impl<X> Len for X {
    fn len(self) -> usize {
        7
    }
}

#[trust_vc::requires(v.len() == 0)]
#[trust_vc::ensures(result == 0usize)]
fn b1(v: Vec<u64>) -> usize {
    v.len()
}
"#;

/// A `&self` method hides `Vec::push(&mut self)`, and a by-value `eq` hides
/// `PartialEq::eq(&self)`.
const SRC_STD_RECEIVERS: &str = r#"
#![allow(dead_code, unused)]
trait P {
    fn push(&self, x: u64);
}
impl P for Vec<u64> {
    fn push(&self, _x: u64) {}
}
trait MyEq {
    fn eq(self, other: &u64) -> bool;
}
impl MyEq for u64 {
    fn eq(self, _other: &u64) -> bool {
        false
    }
}

#[trust_vc::ensures(true)]
fn p1() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    assert!(v.len() == 1);
}

#[trust_vc::ensures(true)]
fn e1(x: u64) {
    assert!(x.eq(&x));
}
"#;

/// A trait method taking `self` hides the inherent `&self` one on a `T`.
const SRC_INHERENT: &str = r#"
#![allow(dead_code, unused)]
#[derive(Clone, Copy)]
struct T {
    v: u64,
}
impl T {
    #[trust_vc::ensures(result == 4u64)]
    fn w(&self) -> u64 {
        4
    }
}
trait B1 {
    fn w(self) -> u64;
}
impl B1 for T {
    fn w(self) -> u64 {
        9
    }
}

#[trust_vc::ensures(result == 4u64)]
fn f1(t: T) -> u64 {
    t.w()
}
"#;

/// The trait method takes `&self` too, so the inherent one wins.
const SRC_INHERENT_TWIN: &str = r#"
#![allow(dead_code, unused)]
#[derive(Clone, Copy)]
struct T {
    v: u64,
}
impl T {
    #[trust_vc::ensures(result == 4u64)]
    fn w(&self) -> u64 {
        4
    }
}
trait B1 {
    fn w(&self) -> u64;
}
impl B1 for T {
    fn w(&self) -> u64 {
        9
    }
}

#[trust_vc::ensures(result == 4u64)]
fn f1(t: T) -> u64 {
    t.w()
}
"#;

/// A trait `eq(self)` hides the derived `PartialEq::eq(&self)`.
const SRC_DERIVED_EQ: &str = r#"
#![allow(dead_code, unused)]
#[derive(PartialEq, Eq, Clone, Copy)]
struct S {
    v: u64,
}
trait MyEq {
    fn eq(self, other: &S) -> bool;
}
impl MyEq for S {
    fn eq(self, _other: &S) -> bool {
        false
    }
}

#[trust_vc::ensures(result == true)]
fn e2(s: S) -> bool {
    s.eq(&s)
}
"#;

/// A trait `clone(self)` hides the derived `Clone::clone(&self)`.
const SRC_DERIVED_CLONE: &str = r#"
#![allow(dead_code, unused)]
#[derive(Clone, Copy)]
struct S {
    v: u64,
}
trait MyClone {
    fn clone(self) -> S;
}
impl MyClone for S {
    fn clone(self) -> S {
        S { v: 7u64 }
    }
}

#[trust_vc::ensures(result == s.v)]
fn c2(s: S) -> u64 {
    let t = s.clone();
    t.v
}
"#;

/// `Iterator::count(self)` hides the inherent `C::count(&self)`.
const SRC_ITERATOR: &str = r#"
#![allow(dead_code, unused)]
struct C {
    n: u64,
}
impl Iterator for C {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        None
    }
}
impl C {
    #[trust_vc::ensures(result == 5usize)]
    fn count(&self) -> usize {
        5
    }
}

#[trust_vc::ensures(result == 5usize)]
fn i2(c: C) -> usize {
    c.count()
}
"#;

/// An impl body that the conformance lane reads with `x.clone()` as `x`.
const SRC_CONFORMANCE: &str = r#"
#![allow(dead_code, unused)]
trait MyClone {
    fn clone(self) -> Self;
}
impl MyClone for u64 {
    fn clone(self) -> Self {
        7
    }
}
#[trust_vc::trait_spec]
trait Get {
    #[trust_vc::ensures(result == 3u64)]
    fn get(&self) -> u64;
}
struct S;
#[trust_vc::trait_impl]
impl Get for S {
    fn get(&self) -> u64 {
        let x: u64 = 3u64;
        x.clone()
    }
}
"#;

/// The same with the trait's method renamed.
const SRC_CONFORMANCE_TWIN: &str = r#"
#![allow(dead_code, unused)]
trait MyClone {
    fn my_clone(self) -> Self;
}
impl MyClone for u64 {
    fn my_clone(self) -> Self {
        7
    }
}
#[trust_vc::trait_spec]
trait Get {
    #[trust_vc::ensures(result == 3u64)]
    fn get(&self) -> u64;
}
struct S;
#[trust_vc::trait_impl]
impl Get for S {
    fn get(&self) -> u64 {
        let x: u64 = 3u64;
        x.clone()
    }
}
"#;

#[test]
fn a_method_call_a_trait_may_take_is_never_verified() {
    check_rows(&[
        (SRC_BACKLOG, "h1", Refused),
        (SRC_BACKLOG, "w1", Refused),
        (SRC_BACKLOG, "r1", Refused),
        (SRC_BACKLOG_TWIN, "h1", Verified),
        (SRC_IMPORTED, "h2", Refused),
        (SRC_IMPORTED_TWIN, "h2", Verified),
        (SRC_BLANKET, "b1", Refused),
        (SRC_STD_RECEIVERS, "p1", Refused),
        (SRC_STD_RECEIVERS, "e1", Refused),
        (SRC_INHERENT, "f1", Refused),
        (SRC_INHERENT_TWIN, "f1", Verified),
        (SRC_DERIVED_EQ, "e2", Refused),
        (SRC_DERIVED_CLONE, "c2", Refused),
        (SRC_ITERATOR, "i2", Refused),
        (
            SRC_CONFORMANCE,
            "trait impl conformance Get::get for S",
            Refused,
        ),
        (
            SRC_CONFORMANCE_TWIN,
            "trait impl conformance Get::get for S",
            Verified,
        ),
    ]);
}
