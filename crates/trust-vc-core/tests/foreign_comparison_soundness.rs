// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A comparison in running code of values of a type whose `PartialEq` or
//! `PartialOrd` impl the file does not show runs that impl.
//!
//! The file lane reads `s == s` over a type another file or crate declares as
//! structural equality, so it holds for every `s`. At run time it calls the
//! type's own impl, which the file does not show and which need not be
//! reflexive. Every liar marked `Refused` below was `Verified`, and each one
//! panics when built with an `S` whose `eq` returns `false`: the backlog
//! program `l4` (`assert!(s == s)`), an `if`, a returned comparison,
//! `assert_eq!`, `!=`, a copy compared with the original, a tuple, an
//! `Option`, a `Vec`, a `let`, a struct of the file that derives `PartialEq`
//! and holds an `S`, and a caller of a function of the file whose body
//! compares. Each is now refused. The one-line twins over `u64` (`l4u`,
//! `e11u`), `String`, `Vec<u64>` and a struct of the file that derives
//! `PartialEq` over integers still verify, and a refutation is kept. A
//! comparison of a field of a struct that holds an `S` (`k3`) is refused
//! too, because the reading cannot tell the field's type.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "tvc_foreign_comparison_{}_{}_{seq}",
        std::process::id(),
        func
    ));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    let path = dir.join("lib.rs");
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_dir_all(&dir);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program whose comparison runs an impl the file does not show.
    Refused,
    /// A false program that another rule or the lowering already keeps from
    /// verifying.
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
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refused => matches!(
                &r,
                Ok(VerifyResult::Error { message }) if message.starts_with("foreign comparison")
            ),
            Expect::NotVerified => !matches!(r, Ok(VerifyResult::Verified)),
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

use Expect::{NotVerified, Refused, Refuted, Verified};

/// `S` and `C` are declared in `other.rs`, which the file lane does not read.
const SRC_FOREIGN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use other::{C, S};

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l4(s: S) -> u64 {
    assert!(s == s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l4u(s: u64) -> u64 {
    assert!(s == s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e1(s: S) -> u64 {
    if s == s { 0u64 } else { 1u64 }
}

#[trust_vc::contract(ensures(r), returns(r))]
fn e2(s: S) -> bool {
    s == s
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e3(s: S) -> u64 {
    assert_eq!(s, s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e4(s: S) -> u64 {
    assert!(s.eq(&s));
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e5(s: S) -> u64 {
    assert!(!(s != s));
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e6(s: S) -> u64 {
    let t = s;
    assert!(t == s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e7(s: S) -> u64 {
    let p = (s, 1u64);
    assert!(p == p);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e8(s: S) -> u64 {
    let o = Some(s);
    assert!(o == o);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e9(v: Vec<S>) -> u64 {
    assert!(v == v);
    0u64
}

fn same(s: &S) -> bool {
    s == s
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e11(s: S) -> u64 {
    assert!(same(&s));
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn same2(s: S) -> u64 {
    if s == s { 0u64 } else { 1u64 }
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e11b(s: S) -> u64 {
    let v = same2(s);
    assert!(v == 0u64);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn same2u(s: u64) -> u64 {
    if s == s { 0u64 } else { 1u64 }
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e11u(s: u64) -> u64 {
    let v = same2u(s);
    assert!(v == 0u64);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e12(s: S) -> u64 {
    let v = vec![s];
    assert!(v.contains(&s));
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e13() -> u64 {
    let a = other::make();
    assert!(a == a);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e14(s: S) -> u64 {
    assert!(s <= s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e15() -> u64 {
    assert!(C == C);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e18(s: S) -> u64 {
    let b = s == s;
    assert!(b);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t1(s: String) -> u64 {
    assert!(s == s);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t2(v: Vec<u64>) -> u64 {
    assert!(v == v);
    0u64
}

#[trust_vc::contract(ensures(r == 1u64), returns(r))]
fn x1(s: S) -> u64 {
    if s == s { 0u64 } else { 1u64 }
}
"#;

/// `S` comes from another crate; the file declares no out-of-line module.
const SRC_CRATE: &str = r#"
#![allow(dead_code, unused)]
use dep::S;

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn k1(s: S) -> u64 {
    assert!(s == s);
    0u64
}

#[derive(PartialEq, Clone, Copy)]
pub struct W {
    pub s: S,
    pub n: u64,
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn k2(w: W) -> u64 {
    assert!(w == w);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn k3(w: W) -> u64 {
    assert!(w.n == w.n);
    0u64
}

#[derive(PartialEq, Clone, Copy)]
pub struct Q {
    pub a: u64,
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn q1(q: Q) -> u64 {
    assert!(q == q);
    0u64
}
"#;

#[test]
fn a_comparison_in_running_code_of_a_type_another_file_declares_is_not_verified() {
    check_table(
        SRC_FOREIGN,
        &[
            // The backlog program and its one-line twin over `u64`.
            ("l4", Refused),
            ("l4u", Verified),
            // More spellings and positions.
            ("e1", Refused),
            ("e2", Refused),
            ("e3", Refused),
            ("e5", Refused),
            ("e6", Refused),
            ("e7", Refused),
            ("e8", Refused),
            ("e9", Refused),
            ("e18", Refused),
            // A function of the file that compares, its caller, and their
            // twins over `u64`.
            ("same2", Refused),
            ("e11b", Refused),
            ("same2u", Verified),
            ("e11u", Verified),
            // The lowering or another rule already keeps these from verifying.
            ("e4", NotVerified),
            ("e11", NotVerified),
            ("e12", NotVerified),
            ("e13", NotVerified),
            ("e14", NotVerified),
            ("e15", NotVerified),
            // True twins.
            ("t1", Verified),
            ("t2", Verified),
            // A refutation is kept.
            ("x1", Refuted),
        ],
    );
}

#[test]
fn a_comparison_in_running_code_of_a_type_another_crate_declares_is_not_verified() {
    check_table(
        SRC_CRATE,
        &[
            ("k1", Refused),
            // A struct of the file that derives `PartialEq` over an `S`.
            ("k2", Refused),
            // The cost: its `u64` field is compared, which is true.
            ("k3", Refused),
            // The twin of `k2` over integers.
            ("q1", Verified),
        ],
    );
}
