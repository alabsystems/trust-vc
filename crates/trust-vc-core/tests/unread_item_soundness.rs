// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An impl, a trait or a type the lane does not read.
//!
//! The lane takes the impls, traits and types a file shows to be all there
//! are. A macro expansion, a derive or attribute macro from another crate, and
//! an `impl` or `trait` written inside a block are not shown, so `p == p` was
//! read as structural equality under a macro that emits `impl PartialEq`
//! returning `false`, `x.clone()` on a `u64` as `Clone::clone` under a macro
//! that declares a `MyClone` trait for `u64`, and `u64` as the primitive under
//! a macro that expands to `type u64 = u8;`. Each such program was `Verified`.
//! A file that can hold such an item is now refused a `Verified` answer. The
//! file's own `macro_rules!` macros whose expansion holds no item the lane
//! misreads are read through, so a file that uses one still verifies.
//!
//! Every liar below was `Verified` on main and fails at run time with the
//! arguments its comment gives (compiled with `trustc`, overflow checks on).
//! Every twin is true and must verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_unread_item_{}_{}_{seq}.rs",
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
    /// A false program refused because its file can hold an unread item.
    Unread,
}

/// The tag of the refusal.
const UNREAD: &str = "unread item";

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(300).collect::<String>())
        }
        Ok(other) => format!("{:.300}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(300).collect::<String>()),
    }
}

fn refused_with(r: &Result<VerifyResult, String>, needle: &str) -> bool {
    match r {
        Ok(VerifyResult::Error { message }) | Err(message) => message.contains(needle),
        _ => false,
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Unread => refused_with(&r, UNREAD),
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

use Expect::{Unread, Verified};

/// The backlog program: a macro emits `impl PartialEq` whose `eq` is false.
const SRC_MACRO_EQ: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! peq {
    ($t:ty) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                false
            }
        }
    };
}

pub struct P {
    pub a: u64,
}
peq!(P);

// q1(P { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn q1(p: P) {
    assert!(p == p);
}
"#;

/// [`SRC_MACRO_EQ`] with the macro invocation replaced by a written impl.
const SRC_MACRO_EQ_TWIN: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! peq {
    ($t:ty) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                false
            }
        }
    };
}

pub struct P {
    pub a: u64,
}
impl PartialEq for P { fn eq(&self, other: &Self) -> bool { self.a == other.a } }

#[trust_vc::ensures(true)]
pub fn q1(p: P) {
    assert!(p == p);
}
"#;

/// A macro emits an `impl PartialEq` that compares one field.
const SRC_MACRO_FIELD_EQ: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! peq_a {
    ($t:ident) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                self.a == other.a
            }
        }
    };
}

pub struct K {
    pub a: u64,
    pub v: u64,
}
peq_a!(K);

// k3(K { a: 0, v: 1 }, K { a: 0, v: 2 }) fails its assertion.
#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
pub fn k3(x: K, y: K) {
    assert!(x.v == y.v);
}

// k4(K { a: 0, v: 1 }, K { a: 0, v: 2 }) fails its assertion.
#[trust_vc::ensures(true)]
pub fn k4(x: K, y: K) {
    if x == y {
        assert!(x.v == y.v);
    }
}
"#;

/// A macro declares a trait whose `clone` takes over `x.clone()` on `u64`.
const SRC_MACRO_TRAIT: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! myclone {
    () => {
        trait MyClone {
            fn clone(self) -> Self;
        }
        impl MyClone for u64 {
            fn clone(self) -> Self {
                7
            }
        }
    };
}
myclone!();

// h1(0) fails its assertion.
#[trust_vc::ensures(true)]
pub fn h1(x: u64) {
    let y = x.clone();
    assert!(y == x);
}
"#;

/// A macro rebinds `u64`, directly and through a fragment.
const SRC_MACRO_TYPE: &str = r#"
#![allow(dead_code, unused, unused_variables, non_camel_case_types)]

macro_rules! d {
    () => {
        type u64 = u8;
    };
}
d!();

// mr1(255) panics: `u64` is `u8` here, so 127 + 200 overflows.
#[trust_vc::ensures(true)]
pub fn mr1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

const SRC_MACRO_ALIAS: &str = r#"
#![allow(dead_code, unused, unused_variables, non_camel_case_types)]

macro_rules! alias {
    ($n:ident, $t:ty) => {
        type $n = $t;
    };
}
alias!(u64, u8);

// f1(255) panics.
#[trust_vc::ensures(true)]
pub fn f1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

/// A macro declares a struct named `u8` whose `Display` counts its calls, and
/// a macro in a module renames `u8` to `u64` there.
const SRC_MACRO_RECEIVER: &str = r#"
#![allow(dead_code, unused, unused_variables, non_camel_case_types)]
use std::cell::Cell;

macro_rules! mk {
    () => {
        pub struct u8(pub Cell<i32>);
        impl std::fmt::Display for u8 {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.set(self.0.get() + 1);
                write!(f, "x")
            }
        }
        impl PartialEq for u8 {
            fn eq(&self, other: &Self) -> bool {
                self.0.get() == other.0.get()
            }
        }
    };
}
mk!();

// mq1(u8(Cell::new(0)), u8(Cell::new(0))) fails its assertion.
#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
pub fn mq1(x: u8, y: u8) {
    x.to_string();
    assert!(x == y);
}

macro_rules! ren {
    () => {
        use core::primitive::u8 as u64;
    };
}
mod inner {
    ren!();

    // inner::mr2(255) panics.
    #[trust_vc::ensures(true)]
    pub fn mr2(a: u8) {
        let y = (a as u64) / 2 + 200;
    }
}
"#;

/// The impl sits in a statement of another function, and in an expression
/// macro that expands to a block.
const SRC_MACRO_POSITIONS: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! peq {
    ($t:ty) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                false
            }
        }
    };
}

pub struct Q {
    pub a: u64,
}
pub fn other_q() {
    peq!(Q);
}

// s1(Q { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn s1(q: Q) {
    assert!(q == q);
}
"#;

const SRC_MACRO_BLOCK: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! blk {
    ($t:ty) => {{
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                false
            }
        }
        0u64
    }};
}

pub struct R {
    pub a: u64,
}
pub fn other_r() -> u64 {
    let z = blk!(R);
    z
}

// e1(R { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn e1(r: R) {
    assert!(r == r);
}
"#;

/// Impls written inside a block: a function body, a `const _` initializer
/// and an `assert!` argument.
const SRC_BLOCK_IMPL: &str = r#"
#![allow(dead_code, unused, unused_variables)]

pub struct W {
    pub a: u64,
}
pub fn other_w() {
    impl PartialEq for W {
        fn eq(&self, other: &Self) -> bool {
            false
        }
    }
}

// w1(W { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn w1(w: W) {
    assert!(w == w);
}
"#;

const SRC_CONST_IMPL: &str = r#"
#![allow(dead_code, unused, unused_variables)]

pub struct C {
    pub a: u64,
}
const _: () = {
    impl PartialEq for C {
        fn eq(&self, other: &Self) -> bool {
            false
        }
    }
};

// c1(C { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn c1(c: C) {
    assert!(c == c);
}
"#;

const SRC_ASSERT_IMPL: &str = r#"
#![allow(dead_code, unused, unused_variables)]

pub struct A2 {
    pub a: u64,
}
pub fn other_a2() {
    assert!({
        impl PartialEq for A2 {
            fn eq(&self, other: &Self) -> bool {
                false
            }
        }
        true
    });
}

// a1(A2 { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn a1(x: A2) {
    assert!(x == x);
}
"#;

/// A derive and an attribute macro from another crate can emit the same
/// impl. Neither can run without that crate, so these are refused on the
/// same reading rather than shown to fail.
const SRC_FOREIGN_DERIVE: &str = r#"
#![allow(dead_code, unused, unused_variables)]

#[derive(Clone, Copy, other_crate::NeverEq)]
pub struct P {
    pub a: u64,
}

#[trust_vc::ensures(true)]
pub fn d1(p: P) {
    assert!(p == p);
}
"#;

const SRC_FOREIGN_ATTRIBUTE: &str = r#"
#![allow(dead_code, unused, unused_variables)]

#[other_crate::never_eq]
pub struct P {
    pub a: u64,
}

#[trust_vc::ensures(true)]
pub fn m1(p: P) {
    assert!(p == p);
}
"#;

/// The twins: the same claims in a file that shows every item. It invokes
/// macros of its own whose expansions hold no item the lane misreads (one
/// declares a struct in a module), and std and toolchain macros.
const SRC_TWINS: &str = r#"
#![allow(dead_code, unused, unused_variables)]

macro_rules! double {
    ($e:expr) => {
        $e * 2u64
    };
}

mod sibling {
    macro_rules! decl_t {
        () => {
            pub struct T {
                pub y: u8,
            }
        };
    }
    decl_t!();
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct P {
    pub a: u64,
}

pub fn g(x: u64) -> u64 {
    let v = vec![x];
    println!("{}", v.len());
    double!(x)
}

#[trust_vc::ensures(true)]
pub fn t1(p: P) {
    assert!(p == p);
}

#[trust_vc::ensures(true)]
pub fn t2(x: u64) {
    let y = x.clone();
    assert!(y == x);
}

#[trust_vc::ensures(true)]
pub fn t3(a: u8) {
    let y = (a as u64) / 2 + 200;
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
pub fn t4(x: P, y: P) {
    assert!(x.a == y.a);
}
"#;

#[test]
fn a_macro_that_emits_an_item_refuses_its_file() {
    check_table(SRC_MACRO_EQ, &[("q1", Unread)]);
    check_table(SRC_MACRO_FIELD_EQ, &[("k3", Unread), ("k4", Unread)]);
    check_table(SRC_MACRO_TRAIT, &[("h1", Unread)]);
    check_table(SRC_MACRO_TYPE, &[("mr1", Unread)]);
    check_table(SRC_MACRO_ALIAS, &[("f1", Unread)]);
    check_table(SRC_MACRO_RECEIVER, &[("mq1", Unread), ("mr2", Unread)]);
    check_table(SRC_MACRO_POSITIONS, &[("s1", Unread)]);
    check_table(SRC_MACRO_BLOCK, &[("e1", Unread)]);
}

#[test]
fn an_impl_written_in_a_block_refuses_its_file() {
    check_table(SRC_BLOCK_IMPL, &[("w1", Unread)]);
    check_table(SRC_CONST_IMPL, &[("c1", Unread)]);
    check_table(SRC_ASSERT_IMPL, &[("a1", Unread)]);
}

#[test]
fn a_foreign_derive_or_attribute_refuses_its_file() {
    check_table(SRC_FOREIGN_DERIVE, &[("d1", Unread)]);
    check_table(SRC_FOREIGN_ATTRIBUTE, &[("m1", Unread)]);
}

#[test]
fn a_file_that_shows_every_item_still_verifies() {
    check_table(SRC_MACRO_EQ_TWIN, &[("q1", Verified)]);
    check_table(
        SRC_TWINS,
        &[
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
            ("t4", Verified),
        ],
    );
}
