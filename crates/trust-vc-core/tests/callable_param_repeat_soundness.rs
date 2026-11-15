// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A parameter of a callable type evaluated twice may return two different
//! values.
//!
//! The lane reads a call `f(x)` of an `F: Fn(..)` parameter as one
//! application of one function symbol, so two calls with equal arguments were
//! the same term and the lane took them to be equal. An `Fn` closure can read
//! shared state: every liar below is well typed and false at run time for a
//! closure that returns `N.fetch_add(1, SeqCst)`, or that bumps a `Cell` it
//! borrows. `v14`, `v3`, `v7`, `v8`, `v13` and `v21` fail an `assert!` and
//! `v2` underflows. Each one was `Verified` before, and each is now refused.
//! One evaluation is one term, which is sound, so the true twins that
//! evaluate each callable parameter once still verify, and a refutation is
//! kept. Every application of a callable parameter also proves its requires
//! at the call, so each fixture declares the requires of what it applies.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_callable_param_repeat_{}_{}_{seq}.rs",
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
    /// A false program whose `Verified` answer is refused by this rule.
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
                    if message.starts_with("bodiless call repeated")
                        && message.contains("callable type")
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

#[trust_vc::requires(f.requires(()))]
fn v14<F: Fn() -> u64>(f: F) {
    let a = f();
    let b = f();
    assert!(a == b);
}

#[trust_vc::requires(f.requires(()))]
fn v2<F: Fn() -> u64>(f: F) -> u64 {
    if f() > 5u64 { f() - 5u64 } else { 0u64 }
}

#[trust_vc::requires(f.requires(()))]
fn v3(f: impl Fn() -> u64) {
    let a = f();
    let b = f();
    assert!(a == b);
}

#[trust_vc::requires(f.requires(()))]
fn v7<F>(f: F)
where
    F: Fn() -> u64,
{
    let a = f();
    let b = f();
    assert!(a == b);
}

#[trust_vc::requires(f.requires(()))]
fn v8<F: Fn() -> u64>(f: F) {
    let first = f();
    let mut i = 0u64;
    while i < 3u64 {
        assert!(f() == first);
        i = i + 1u64;
    }
}

#[trust_vc::requires(x == y && f.requires((x,)) && f.requires((y,)))]
#[trust_vc::ensures(true)]
fn v13<F: Fn(u64) -> u64>(f: F, x: u64, y: u64) {
    assert!(f(x) == f(y));
}

#[trust_vc::requires(f.requires((x,)))]
#[trust_vc::ensures(result == f(x))]
fn v21<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
    f(x)
}

#[trust_vc::requires(f.requires(()))]
fn t1<F: Fn() -> u64>(f: F) -> u64 {
    let a = f();
    a
}

#[trust_vc::requires(f.requires((3u64,)))]
fn t2<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    assert!(a == a);
}

#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn t3<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    f(a)
}

#[trust_vc::requires(f.requires((3u64,)) && f.requires((4u64,)))]
fn x1<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(4u64);
    assert!(a == b);
}
"#;

#[test]
fn a_callable_parameter_evaluated_twice_is_refused_and_one_evaluation_verifies() {
    check_table(
        SRC,
        &[
            // The backlog program: `f()` twice.
            ("v14", Refused),
            ("v2", Refused),
            ("v3", Refused),
            ("v7", Refused),
            ("v8", Refused),
            ("v13", Refused),
            ("v21", Refused),
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
            // Two calls with different arguments: false, and still refuted.
            ("x1", Refuted),
        ],
    );
}
