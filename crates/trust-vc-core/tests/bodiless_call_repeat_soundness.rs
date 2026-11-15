// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A bodiless exec function evaluated twice may return two different values.
//!
//! The lane reads a call of a function whose body it does not read
//! (`#[external_body]`, `#[external]`, or a function inside a marked `impl`
//! or `mod`) as one application of one function symbol, so two calls with
//! equal arguments were the same term and the lane took them to be equal.
//! Every liar below is well typed and false at run time for a body that
//! meets its contract, such as one that returns a counter (`read_input`
//! returning `N.fetch_add(1, SeqCst) % 100`): `d8` and `c1` fail their
//! `assert!`, `z1` and `z9` underflow. Each one was `Verified` before, and
//! each is now refused. One evaluation is one term, which is sound, so the
//! true twins that evaluate each such function once still verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_bodiless_call_repeat_{}_{}_{seq}.rs",
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
            ),
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

use Expect::{Refused, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::external_body]
#[trust_vc::ensures(result >= 2u64)]
fn r(x: u64) -> u64 {
    unimplemented!()
}

#[trust_vc::external_body]
#[trust_vc::ensures(result < 100u64)]
fn read_input() -> u64 {
    unimplemented!()
}

#[trust_vc::external_body]
#[trust_vc::ensures(result < 100u64)]
fn read_other() -> u64 {
    unimplemented!()
}

fn wrap() -> u64 {
    read_input()
}

fn five() -> u64 {
    5u64
}

struct S {
    k: u64,
}

impl S {
    #[trust_vc::external_body]
    #[trust_vc::ensures(result < 100u64)]
    fn get(&self) -> u64 {
        unimplemented!()
    }

    #[trust_vc::ensures(result == 0u64)]
    fn q(&self) -> u64 {
        let a = read_input();
        let b = read_input();
        a - b
    }
}

#[trust_vc::external_body]
impl S {
    fn get2(&self) -> u64 {
        unimplemented!()
    }
}

#[trust_vc::ensures(true)]
fn d8() {
    let a = r(1u64);
    let b = r(1u64);
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn z1() -> u64 {
    read_input() - read_input()
}

#[trust_vc::ensures(result == 0u64)]
fn z9() -> u64 {
    let x = read_input();
    let y = read_input();
    x - y
}

#[trust_vc::ensures(true)]
fn z2() {
    if read_input() > 5u64 {
        let v = read_input();
        assert!(v > 5u64);
    }
}

#[trust_vc::ensures(true)]
fn c1(x: u64, y: u64) {
    if x == y {
        let a = r(x);
        let b = r(y);
        assert!(a == b);
    }
}

#[trust_vc::ensures(true)]
fn w1() {
    let a = wrap();
    let b = read_input();
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn m1(s: S) {
    let a = s.get();
    let b = s.get();
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn m2(s: S) {
    let a = s.get2();
    let b = s.get2();
    assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l1() {
    let first = read_input();
    let mut i = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64);
        let v = read_input();
        assert!(v == first);
        i = i + 1u64;
    }
}

#[trust_vc::ensures(true)]
fn t1() {
    let a = r(1u64);
    assert!(a >= 2u64);
}

#[trust_vc::ensures(result < 200u64)]
fn t2() -> u64 {
    let a = read_input();
    let b = read_other();
    a + b
}

#[trust_vc::ensures(true)]
fn t3() {
    let a = read_input();
    let b = five();
    let c = five();
    assert!(b == c);
    assert!(a < 100u64);
}
"#;

#[test]
fn a_bodiless_function_evaluated_twice_is_refused_and_one_evaluation_verifies() {
    check_table(
        SRC,
        &[
            // The backlog program: `r(1u64)` twice.
            ("d8", Refused),
            ("z1", Refused),
            ("z9", Refused),
            ("z2", Refused),
            ("c1", Refused),
            ("w1", Refused),
            ("m1", Refused),
            ("m2", Refused),
            ("q", Refused),
            ("l1", Refused),
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
        ],
    );
}
