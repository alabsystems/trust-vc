// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A method call or a comparison on a value of a generic type runs an impl
//! the caller chooses.
//!
//! The lane reads `t.read()` on `t: &T` as one application of the trait's
//! function symbol, so two calls were the same term, and it reads `x == y` on
//! `x: T` as structural equality, which is reflexive and does not change when
//! `x.to_string()` runs in between. An impl can read and write a `Cell`, and a
//! `PartialEq` impl need not be reflexive: every liar below was `Verified`
//! and is false for some impl. Compiled with `trustc`, `qc3`, `qc5`, `qc6`,
//! `qc7`, `a3` and `a4` panic for a type whose `Display` or `read` bumps a
//! `Cell`, and `e0(f64::NAN)` returns false. Each one is now refused. One
//! evaluation of a method is one term, and a comparison in a contract is
//! spec equality, so the true twins still verify, and a refutation is kept.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_generic_receiver_{}_{}_{seq}.rs",
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
    /// A false program that evaluates a method of a generic value twice.
    RefusedRepeat,
    /// A false program that compares generic values in executable code.
    RefusedComparison,
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
            Expect::RefusedRepeat => matches!(
                &r,
                Ok(VerifyResult::Error { message })
                    if message.starts_with("bodiless call repeated")
                        && message.contains("generic type")
            ),
            Expect::RefusedComparison => matches!(
                &r,
                Ok(VerifyResult::Error { message }) if message.starts_with("generic comparison")
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

use Expect::{RefusedComparison, RefusedRepeat, Refuted, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused)]
use std::fmt::Display;

#[trust_vc::trait_spec]
trait Tr {
    fn read(&self) -> u64;
    fn bump(&self);
}

#[trust_vc::requires(x == y)]
fn qc3<W: Display + PartialEq>(x: W, y: W) {
    x.to_string();
    assert!(x == y);
}

#[trust_vc::requires(x == y)]
fn qc3t<T: Display + PartialEq>(x: T, y: T) {
    x.to_string();
    assert!(x == y);
}

#[trust_vc::requires(x == y)]
fn qc5<W: Display + PartialEq>(x: W, y: W) {
    let p = (x, y);
    p.0.to_string();
    assert!(p.0 == p.1);
}

#[trust_vc::requires(p.0 == p.1)]
fn qc6<W: Display + PartialEq>(p: (W, W)) {
    p.0.to_string();
    assert!(p.0 == p.1);
}

#[trust_vc::ensures(true)]
fn a3<T: Tr>(t: T) {
    let a = t.read();
    t.bump();
    let b = t.read();
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn a4<T: Tr>(t: T) {
    let a = t.read();
    let b = t.read();
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn i1(t: impl Tr) {
    let a = t.read();
    let b = t.read();
    assert!(a == b);
}

#[trust_vc::ensures(result == t.read())]
fn r1<T: Tr>(t: &T) -> u64 {
    t.read()
}

#[trust_vc::ensures(result)]
fn e0<T: PartialEq>(x: T) -> bool {
    x == x
}

#[trust_vc::ensures(true)]
fn e1<T: PartialEq>(x: T, y: T) {
    if x == y {
        assert!(x == y);
    }
}

#[trust_vc::ensures(result == 5u64)]
fn x1<T: Tr>(t: &T) -> u64 {
    t.read()
}

#[trust_vc::ensures(true)]
fn t1<T: Tr>(t: &T) -> u64 {
    t.read()
}

#[trust_vc::ensures(true)]
fn t2<T: Tr>(t: &T) {
    let a = t.read();
    assert!(a == a);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(result == x)]
fn t3<T: PartialEq>(x: T, y: T) -> T {
    y
}

struct H<W>(W);

impl<W: Display + PartialEq> H<W> {
    #[trust_vc::requires(x == y)]
    fn qc7(&self, x: W, y: W) {
        x.to_string();
        assert!(x == y);
    }
}
"#;

#[test]
fn a_method_or_comparison_on_a_generic_value_is_not_verified_by_reading_it_as_a_function() {
    check_table(
        SRC,
        &[
            // The backlog programs.
            ("qc3", RefusedComparison),
            ("qc3t", RefusedComparison),
            ("qc5", RefusedComparison),
            ("qc6", RefusedComparison),
            ("qc7", RefusedComparison),
            ("a3", RefusedRepeat),
            ("a4", RefusedRepeat),
            // More spellings of the same holes.
            ("i1", RefusedRepeat),
            ("r1", RefusedRepeat),
            ("e0", RefusedComparison),
            ("e1", RefusedComparison),
            // A refutation is kept.
            ("x1", Refuted),
            // True twins.
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
        ],
    );
}
