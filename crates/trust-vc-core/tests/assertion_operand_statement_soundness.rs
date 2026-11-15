// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `assert!`, `assert_eq!` and `assert_ne!` evaluate their condition at run
//! time, and so do `trust_vc::assert!`, `trust_vc::invariant!` and
//! `trust_vc::invariant_except_break!`, which expand to `assert!` outside
//! `cfg(test)`. The lane only renders an assertion condition, and the
//! rendering of a block keeps its tail value and drops what the block's other
//! statements do. So `assert!({ let y = x + 1u64; true })` emitted no overflow
//! check and was `Verified`, although it panics at `u64::MAX`; the same held for
//! a division, an index, an `unwrap`, a callee precondition and the `add` and
//! `add_assign` methods, in a nested block, an `if` branch, `assert_eq!`,
//! `assert_ne!`, a loop invariant and a `loop_decreases!` measure.
//!
//! Such a statement in an exec body is now refused, unless it is an item or a
//! `let` whose initializer runs nothing that can panic. Every liar below is well
//! typed; run with `trustc` and the argument named, each one panics: `a2`,
//! `a3`, `a4`, `a5`, `a6`, `a7`, `a8`, `a9` and `a10` at `x == u64::MAX`,
//! `a11` at `d == 0`, `a12` at `x == 3`, `a13` at `o == None`, `a14` at any
//! `x`, `a16` and `a17` at `x == u64::MAX`, and `a18` and `a19` (whose
//! `loop_decreases!` measure is evaluated each iteration) at `n == u64::MAX`.
//! Every twin is true and was verified before the change.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_assertion_operand_stmt_{}_{}_{seq}.rs",
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
    /// Refused by the assertion-operand statement rule.
    Refused,
    /// A false program the lane already refutes.
    Refuted,
}

const REFUSAL: &str = "the lane reads only the block's value";

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

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refused => match &r {
                Ok(VerifyResult::Error { message }) => message.contains(REFUSAL),
                Err(message) => message.contains(REFUSAL),
                _ => false,
            },
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

const LIARS: &str = r#"
#![allow(dead_code, unused)]
use std::ops::{Add, AddAssign};

#[trust_vc::requires(x > 0u64)]
#[trust_vc::ensures(result == 10u64 / x)]
fn need(x: u64) -> u64 {
    10u64 / x
}

fn a2(x: u64) {
    assert!({ let y = x + 1u64; true });
}

fn a3(x: u64) {
    assert!({ x + 1u64; true });
}

fn a4(x: u64) {
    assert!({ x.add(1u64); true });
}

fn a5(mut x: u64) {
    assert!({ x.add_assign(1u64); true });
}

fn a6(x: u64) {
    assert_eq!({ let y = x + 1u64; 0u64 }, 0u64);
}

fn a7(x: u64) {
    assert_ne!({ x + 1u64; 1u64 }, 0u64);
}

fn a8(x: u64) {
    trust_vc::assert!({ let y = x + 1u64; true });
}

fn a9(x: u64) {
    assert!({ { x + 1u64; } true });
}

fn a10(x: u64) {
    assert!(if x > 5u64 { let y = x + 1u64; true } else { true });
}

fn a11(x: u64, d: u64) {
    assert!({ let y = x / d; true });
}

fn a12(x: u64, a: [u64; 3]) {
    assert!({ let y = a[x as usize]; true });
}

fn a13(o: Option<u64>) {
    assert!({ let y = o.unwrap(); true });
}

fn a14(x: u64) {
    assert!({ need(0u64); true });
}

#[trust_vc::requires(x < 10u64)]
fn a15(x: u64) {
    assert!({ let y = x + 1u64; y > x });
}

fn a16(x: u64) {
    assert!({ let o = Result::<u64, u64>::Ok(x + 1u64); true });
}

fn a17(x: u64) {
    assert!({ let t = (0u64, x + 1u64); true });
}

fn a18(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n && { let m = n + 1u64; true });
        i = i + 1u64;
    }
}

fn a19(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::loop_decreases!({ let m = n + 1u64; n - i });
        i = i + 1u64;
    }
}

fn r1(x: u64) {
    assert!({ x + 1u64 > x });
}

fn r2(x: u64) {
    assert!({ let y = x; y + 1u64 > y });
}
"#;

/// The backlog program `a2` and every other statement position are refused,
/// and so is a `let` whose initializer holds arithmetic under a constructor or
/// a tuple (`a16`, `a17`). `a15` is true and verified before the change; its
/// statement is refused too, which is the cost of the rule. `r1`, whose block
/// holds only its tail, and `r2`, whose `let` binds a plain value, are still
/// refuted: the tail is rendered into the condition and checked.
#[test]
fn a_statement_in_an_assertion_operand_block_is_refused() {
    check_table(
        LIARS,
        &[
            ("a2", Refused),
            ("a3", Refused),
            ("a4", Refused),
            ("a5", Refused),
            ("a6", Refused),
            ("a7", Refused),
            ("a8", Refused),
            ("a9", Refused),
            ("a10", Refused),
            ("a11", Refused),
            ("a12", Refused),
            ("a13", Refused),
            ("a14", Refused),
            ("a15", Refused),
            ("a16", Refused),
            ("a17", Refused),
            ("a18", Refused),
            ("a19", Refused),
            ("r1", Refuted),
            ("r2", Refuted),
        ],
    );
}

const TWINS: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::requires(x < 10u64)]
fn t1(x: u64) {
    assert!({ x + 1u64 > x });
}

#[trust_vc::requires(x < 10u64)]
fn t2(x: u64) {
    let b = { let y = x + 1u64; true };
    assert!(b);
}

#[trust_vc::requires(x < 10u64)]
fn t3(x: u64, c: bool) {
    assert!(if c { x + 1u64 > x } else { true });
}

#[trust_vc::requires(x < 10u64)]
fn t4(x: u64) {
    assert!(match x { 0u64 => true, _ => { x - 1u64 < x } });
}

#[trust_vc::requires(x < 10u64)]
fn t5(x: u64) {
    assert_eq!({ x + 1u64 }, x + 1u64);
}

#[trust_vc::proof]
#[trust_vc::requires(x < 10u64)]
fn t6(x: u64) {
    trust_vc::assert!({ let y = x + 1u64; y > x });
}

#[trust_vc::requires(x < 10u64)]
fn t7(x: u64) {
    assert!({ let y = x; y == x });
}

#[trust_vc::requires(x < 10u64)]
fn t8(x: u64) {
    assert!({ let o = Option::<u64>::Some(x); o.is_some() });
}

fn t9(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n && { let m = n; i <= m });
        i = i + 1u64;
    }
}
"#;

/// A block holding only its tail, the same statement in a `let` initializer
/// block, the branches of an `if` and a `match`, a statement in a proof
/// function's assertion, and a `let` that binds a plain value or a std
/// constructor of one (`t7`, `t8`, and `t9` in a loop invariant) still verify.
#[test]
fn a_tail_only_block_or_a_let_block_still_verifies() {
    check_table(
        TWINS,
        &[
            ("t1", Verified),
            ("t2", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("t5", Verified),
            ("t6", Verified),
            ("t7", Verified),
            ("t8", Verified),
            ("t9", Verified),
        ],
    );
}
