// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `while let` pattern binds a new value on every turn, even when an outer
//! binding has the same name.
//!
//! The lane does not project a `while let` payload, and it left the names the
//! pattern binds unbound in the body. Under a parameter or a local of the same
//! name, a read of that name in the body read the outer value instead, so
//! `while let Some(v) = p { let w = v + 1u64; p = None; }` checked `v + 1`
//! against the parameter's `v < 10` and was `Verified`. Such a name now reads
//! as nothing in the body, so every read of it fails closed. A `let` chain in a
//! `while` condition (`while let Some(v) = p && v > 0u64`), whose names the
//! lane read the same way, is refused.
//!
//! Every liar below panics at run time with the arguments its comment gives.
//! Every twin is true and must verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_while_let_pattern_shadow_{}_{}_{seq}.rs",
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
    /// A false program the lane refutes.
    Refuted,
    /// A false program whose read of the pattern's name fails closed.
    Unbound,
    /// A false program refused for its `let` chain.
    LetChain,
}

/// The name the pattern binds, read in the body, is not bound there.
const UNBOUND: &str = "unresolved variable `v`";

/// The refusal of a `let` chain in a `while` condition.
const LET_CHAIN: &str = "a `let` chain in a `while` condition is unsupported";

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
            Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
            Expect::Unbound => refused_with(&r, UNBOUND),
            Expect::LetChain => refused_with(&r, LET_CHAIN),
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

use Expect::{LetChain, Refuted, Unbound, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_variables, unused_assignments)]

// w1(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn w1(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        let w = v + 1u64;
        p = None;
    }
}

// w2(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn w2(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(mut v) = p {
        v += 1u64;
        p = None;
    }
}

// w4(0, (u64::MAX, 0)) panics.
#[trust_vc::requires(v < 10u64)]
fn w4(v: u64, o: (u64, u64)) {
    let mut p = Some(o);
    while let Some((v, _)) = p {
        let w = v + 1u64;
        p = None;
    }
}

// w5(0, Some(10)) fails its assertion.
#[trust_vc::requires(v < 10u64)]
fn w5(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        assert!(v < 10u64);
        p = None;
    }
}

// w6(Some(u64::MAX)) panics: the pattern shadows a local.
fn w6(o: Option<u64>) {
    let v = 0u64;
    let mut p = o;
    while let Some(v) = p {
        let w = v + 1u64;
        p = None;
    }
}

// i1(0, Some(u64::MAX)) fails its invariant.
#[trust_vc::requires(v < 10u64)]
fn i1(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        trust_vc::invariant!(v < 10u64);
        p = None;
    }
}

// c3(0, Some(u64::MAX)) panics.
#[trust_vc::requires(v < 10u64)]
fn c3(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p && v > 0u64 {
        let w = v + 1u64;
        p = None;
    }
}

// x1(1, None) panics; the outer `v` is read after the loop.
#[trust_vc::requires(v < 10u64)]
fn x1(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        p = None;
    }
    let w = v + u64::MAX;
}

#[trust_vc::requires(v < 10u64)]
fn t1(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(u) = p {
        let w = v + 1u64;
        p = None;
    }
}

#[trust_vc::requires(v < 10u64)]
fn t2(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        p = None;
    }
    let w = v + 1u64;
}
"#;

#[test]
fn a_while_let_binding_is_never_read_as_the_outer_binding() {
    check_table(
        SRC,
        &[
            ("w1", Unbound),
            ("w2", Unbound),
            ("w4", Unbound),
            ("w5", Unbound),
            ("w6", Unbound),
            ("i1", Unbound),
            ("c3", LetChain),
            ("x1", Refuted),
            ("t1", Verified),
            ("t2", Verified),
        ],
    );
}
