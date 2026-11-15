// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A pattern binder, closure parameter or `let` binds a new value, even when
//! an outer binding has the same name.
//!
//! The lane bound such a name to the bare name when it could not work out the
//! new value, expecting the bare name to be an unresolved variable. But under
//! a parameter `v` the bare name IS the parameter, so
//! `if let Some(mut v) = o { v += 1u64; }` checked the parameter's value
//! instead of the payload's. The same happened for a `mut` binder in a tuple,
//! slice, struct or `let ... else` pattern, a `mut v @ ..` binder, a match arm,
//! a closure parameter, a `for` loop variable, and a payload of a scrutinee
//! the lane cannot type. Such a binding now reads a fresh symbol that is never
//! declared, so every read of it fails closed.
//!
//! Every liar below is well typed and panics at run time with the arguments
//! the comments give. Every twin is true and must verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_pattern_shadow_{}_{}_{seq}.rs",
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
    /// A panicking program: refuted with a counterexample.
    Counterexample,
    /// Refused because the new binding's value is not modeled.
    Refused,
}

/// The note the lowering adds to an unresolved variable that is a new
/// binding of a name that already denotes a value.
const SHADOW_NOTE: &str = "binds this name again with a value vc_extraction does not model";

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(400).collect::<String>())
        }
        Ok(other) => format!("{:.400}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(400).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
            Expect::Refused => match &r {
                Ok(VerifyResult::Error { message }) => message.contains(SHADOW_NOTE),
                Err(message) => message.contains(SHADOW_NOTE),
                _ => false,
            },
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

use Expect::{Counterexample, Refused, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_variables)]

use std::ops::AddAssign;

struct S {
    a: u64,
    b: u64,
}

#[trust_vc::external_body]
fn g() -> Option<u64> {
    None
}

// y1(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn y1(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        let w = v + 1u64;
    }
}

// y7(0, (u64::MAX, 0)) panics.
#[trust_vc::requires(v < 10u64)]
fn y7(v: u64, o: (u64, u64)) {
    let (mut v, _) = o;
    v += 1u64;
}

// z2(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn z2(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        v += 1u64;
    }
}

// z1(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn z1(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        v.add_assign(1u64);
    }
}

// z6(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn z6(v: u64, o: Option<u64>) {
    match o {
        Some(mut v) => {
            v += 1u64;
        }
        None => {}
    }
}

// y6(0) panics.
#[trust_vc::requires(v < 10u64)]
fn y6(v: u64) {
    let f = |mut v: u64| {
        v += 1u64;
    };
    f(u64::MAX);
}

// p1(0) panics when g returns Some(u64::MAX).
#[trust_vc::requires(v < 10u64)]
fn p1(v: u64) {
    if let Some(v) = g() {
        let w = v + 1u64;
    }
}

// p6(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn p6(v: u64, o: Option<u64>) {
    let Some(mut v) = o else { return };
    v += 1u64;
}

// p8(0, [u64::MAX, 0]) panics.
#[trust_vc::requires(v < 10u64)]
fn p8(v: u64, a: [u64; 2]) {
    let [mut v, _] = a;
    v += 1u64;
}

// p11(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn p11(v: u64, o: Option<u64>) {
    if let Some(mut v @ 0..=u64::MAX) = o {
        v += 1u64;
    }
}

// p12(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn p12(v: u64, o: Option<u64>) {
    match o {
        Some(mut v) if v > 0u64 => {
            let w = v + 1u64;
        }
        _ => {}
    }
}

// p13(0, (u64::MAX, 0)) panics.
#[trust_vc::requires(v < 10u64)]
fn p13(v: u64, o: (u64, u64)) {
    let (mut v, mut u) = o;
    let w = v + 1u64;
}

// q1(0, [u64::MAX, 0, 0]) panics.
#[trust_vc::requires(v < 10u64)]
fn q1(v: u64, a: [u64; 3]) {
    for v in a {
        let w = v + 1u64;
    }
}

// q2(0) panics.
#[trust_vc::requires(v < 10u64)]
fn q2(v: u64) {
    let f = |v| {
        let w = v + 1u64;
    };
    f(u64::MAX);
}

// q3(0) panics when g returns Some(u64::MAX).
#[trust_vc::requires(v < 10u64)]
fn q3(v: u64) {
    match g() {
        Some(v) => {
            let w = v + 1u64;
        }
        None => {}
    }
}

// q6(0, S { a: u64::MAX, b: 0 }) panics.
#[trust_vc::requires(a < 10u64)]
fn q6(a: u64, s: S) {
    let S { mut a, .. } = s;
    a += 1u64;
}

// q7(0, Some(&u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn q7(v: u64, r: Option<&u64>) {
    if let Some(&v) = r {
        let w = v + 1u64;
    }
}

// q8(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn q8(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        if v > 3u64 {
            let w = v + 1u64;
        }
    }
}

// q10(0, Some(10)) fails its assertion.
#[trust_vc::requires(v < 10u64)]
fn q10(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        assert!(v < 10u64);
    }
}

// x1(0, Some(u64::MAX)) panics; the payload is read and refuted.
#[trust_vc::requires(v < 10u64)]
fn x1(v: u64, o: Option<u64>) {
    if let Some(v) = o {
        let w = v + 1u64;
    }
}

// x2(0, Some(11)) returns 11; the value-position match binds its own `v`.
#[trust_vc::requires(v < 10u64)]
#[trust_vc::ensures(result < 11u64)]
fn x2(v: u64, o: Option<u64>) -> u64 {
    match o {
        Some(mut v) => v,
        None => 0u64,
    }
}

#[trust_vc::requires(v < 10u64)]
fn t1(v: u64, o: Option<u64>) { if let Some(mut u) = o { let w = v + 1u64; } }

#[trust_vc::requires(v < 10u64)]
fn t2(v: u64) {
    let mut v = v;
    v += 1u64;
}

#[trust_vc::requires(v < 10u64)]
fn t3(v: u64, a: [u64; 3]) {
    for u in a {
        let w = v + 1u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn t4(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        v = 3u64;
        let w = v + 1u64;
    }
}

#[trust_vc::ensures(result == 5u64)]
fn t5(o: Option<u64>) -> u64 {
    if let Some(mut v) = o {
        v = 5u64;
        v
    } else {
        5u64
    }
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x)]
fn t6(x: u64, o: Option<u64>) -> u64 {
    if let Some(x) = o {
        let _ = x;
    }
    x
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x)]
fn t7(x: u64) -> u64 {
    let r = match Some(x) {
        Some(x) => x,
        None => 0u64,
    };
    r
}

#[trust_vc::requires(x < 100u64 && y < 100u64)]
fn t8(x: u64, y: u64) -> u64 {
    let f = |x: u64| x / 2u64;
    f(y) + x
}
"#;

#[test]
fn shadowing_bindings_never_read_the_outer_value() {
    check_table(
        SRC,
        &[
            ("y1", Refused),
            ("y7", Refused),
            ("z2", Refused),
            ("z1", Refused),
            ("z6", Refused),
            ("y6", Refused),
            ("p1", Refused),
            ("p6", Refused),
            ("p8", Refused),
            ("p11", Refused),
            ("p12", Refused),
            ("p13", Refused),
            ("q1", Refused),
            ("q2", Refused),
            ("q3", Refused),
            ("q6", Refused),
            ("q7", Refused),
            ("q8", Refused),
            ("q10", Refused),
            ("x1", Counterexample),
            ("x2", Counterexample),
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("t5", Verified),
            ("t6", Verified),
            ("t7", Verified),
            ("t8", Verified),
        ],
    );
}
