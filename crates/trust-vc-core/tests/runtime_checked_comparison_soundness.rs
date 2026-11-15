// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A contract clause or assertion the `trust_vc` macros check at run time
//! compares with the operands' own `PartialEq` or `PartialOrd` impl.
//!
//! The lane reads `r == x` in `#[trust_vc::contract(ensures(r == x), ..)]`,
//! and in `trust_vc::assert!` and `invariant!`, over a value of a generic
//! type as structural equality, so `x == x` holds for every `x`. Outside a
//! verification build the macros check such a clause with `assert!` when it
//! calls nothing, and that runs the impl: a generic type's impl is the
//! caller's choice, and a type another file declares has an impl the file
//! does not show. Every liar below was `Verified`, and built with the real
//! macros each one panics on its first call, with a NaN (`t7(f64::NAN)`,
//! `W(f64::NAN).get()`) or with a type whose `eq` returns `false` (`o1`,
//! `l3`). Each is now refused. A generic caller of a function whose checked
//! precondition compares generic values (`c2`) is refused too, since the
//! lane reads the precondition at the call. The one-line twin over `u64`,
//! clauses over strings, std collections and a type deriving `PartialEq`
//! over integers, the attribute spellings the macros do not provide, and a
//! generic function whose checked clause compares integers still verify,
//! and a refutation is kept.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_runtime_checked_comparison_{}_{}_{seq}.rs",
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
    /// A false program whose run-time check compares values the lane reads
    /// structurally.
    Refused,
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
                Ok(VerifyResult::Error { message })
                    if message.starts_with("run-time checked comparison")
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

use Expect::{Refused, Refuted, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused)]
use std::collections::BTreeSet;

#[trust_vc::contract(ensures(r == x), returns(r))]
fn t7<T: PartialEq + Copy>(x: T) -> T {
    x
}

#[trust_vc::contract(ensures(r == x), returns(r))]
fn t7u(x: u64) -> u64 {
    x
}

#[trust_vc::contract(ensures(!(r != x)), returns(r))]
fn ne1<T: PartialEq + Copy>(x: T) -> T {
    x
}

#[trust_vc::contract(ensures(r == p), returns(r))]
fn tup<T: PartialEq + Copy>(p: (T, u64)) -> (T, u64) {
    p
}

#[trust_vc::contract(ensures(r == o), returns(r))]
fn opt<T: PartialEq + Copy>(o: Option<T>) -> Option<T> {
    o
}

#[trust_vc::contract(ensures(r == x), returns(r))]
fn rf<T: PartialEq>(x: &T) -> &T {
    x
}

pub struct W<T>(pub T);

impl<T: PartialEq + Copy> W<T> {
    #[trust_vc::contract(ensures(r == self.0), returns(r))]
    pub fn get(&self) -> T {
        self.0
    }
}

#[trust_vc::contract(requires(a == b), ensures(r == 0u64), returns(r))]
fn g<T: PartialEq>(a: T, b: T) -> u64 {
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn c2<T: PartialEq + Copy>(x: T) -> u64 {
    g(x, x)
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn a1<T: PartialEq>(x: T) -> u64 {
    trust_vc::assert!(x == x);
    0u64
}

#[trust_vc::contract(ensures(r == 3u64), returns(r))]
fn i1<T: PartialEq>(x: T) -> u64 {
    let mut i = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64 && x == x);
        i += 1u64;
    }
    i
}

#[trust_vc::contract(ensures(r == s), returns(r))]
fn o3(s: String) -> String {
    s
}

#[trust_vc::contract(ensures(r == s), returns(r))]
fn o4(s: BTreeSet<u64>) -> BTreeSet<u64> {
    s
}

#[derive(PartialEq, Clone, Copy)]
pub struct Q {
    pub a: u64,
}

#[trust_vc::contract(ensures(r == q), returns(r))]
fn dq(q: Q) -> Q {
    q
}

#[trust_vc::contract(ensures(r == n), returns(r))]
fn ln<T>(v: Vec<T>, n: u64) -> u64 {
    n
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(result == x)]
fn at<T: PartialEq>(x: T, y: T) -> T {
    y
}

#[trust_vc::contract(ensures(r == x), returns(r))]
fn gx<T: PartialEq + Copy>(x: T, y: T) -> T {
    y
}
"#;

/// `S` is declared in `other.rs`, whose `PartialEq` impl this file does not
/// show; there it returns `false`.
const SRC_FOREIGN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use other::S;

#[trust_vc::contract(ensures(r == s), returns(r))]
fn o1(s: S) -> S {
    s
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l3(s: S) -> u64 {
    let t = s;
    trust_vc::assert!(t == t);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l3u(s: u64) -> u64 {
    let t = s;
    trust_vc::assert!(t == t);
    0u64
}
"#;

#[test]
fn a_run_time_check_that_compares_with_an_unread_impl_is_not_verified() {
    check_table(
        SRC,
        &[
            // The backlog program and its one-line twin over `u64`.
            ("t7", Refused),
            ("t7u", Verified),
            // More clauses and positions.
            ("ne1", Refused),
            ("tup", Refused),
            ("opt", Refused),
            ("rf", Refused),
            ("get", Refused),
            ("g", Refused),
            ("c2", Refused),
            ("a1", Refused),
            ("i1", Refused),
            // True twins.
            ("o3", Verified),
            ("o4", Verified),
            ("dq", Verified),
            ("ln", Verified),
            ("at", Verified),
            // A refutation is kept.
            ("gx", Refuted),
        ],
    );
}

#[test]
fn a_run_time_check_that_compares_values_of_a_type_another_file_declares_is_not_verified() {
    check_table(
        SRC_FOREIGN,
        &[("o1", Refused), ("l3", Refused), ("l3u", Verified)],
    );
}
