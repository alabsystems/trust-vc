// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// REPRO: loop-body call-ensures leak. A call inside a loop body leaks its
// `ensures` PAST the (possibly zero-iteration) loop, proving a post-loop
// assert that need not hold. Plus the DECISIVE controls that must NOT regress.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::ensures(x == 7u64)]
fn mk(x: u64) -> u64 { 0u64 }

#[trust_vc::external_body]
#[trust_vc::ensures(x == 7u64)]
fn mk_ext(x: u64) -> u64 { 0u64 }

#[trust_vc::requires(x > 10u64)]
fn need(x: u64) -> u64 { 0u64 }

// ---- LEAK shapes: must NOT verify (post-loop assert reached even at n==0) ----

fn leak_while(n: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = mk(a);
        i = i + 1u64;
    }
    trust_vc::assert!(a == 7u64);
}

fn leak_for(n: u64, a: u64) {
    for _k in 0u64..n {
        let _ = mk(a);
    }
    trust_vc::assert!(a == 7u64);
}

fn leak_bare(cond: bool, a: u64) {
    loop {
        if cond { break; }
        let _ = mk(a);
        break;
    }
    trust_vc::assert!(a == 7u64);
}

fn leak_nested(n: u64, m: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        let mut j = 0u64;
        while j < m {
            let _ = mk(a);
            j = j + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(a == 7u64);
}

fn leak_external_body(n: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = mk_ext(a);
        i = i + 1u64;
    }
    trust_vc::assert!(a == 7u64);
}

#[trust_vc::ensures(a == 7u64)]
fn leak_postcondition(n: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = mk(a);
        i = i + 1u64;
    }
}

// ---- DECISIVE controls: must stay Counterexample (NOT made vacuous) ----

fn false_assert_in_while(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(false);
        i = i + 1u64;
    }
}

fn false_assert_in_for(n: u64) {
    for _k in 0u64..n {
        trust_vc::assert!(false);
    }
}

fn genuinely_false_assert_in_while(n: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(a == 7u64);
        i = i + 1u64;
    }
}

fn unmet_requires_in_while(n: u64, c: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = need(c);
        i = i + 1u64;
    }
}

fn unmet_requires_in_for(n: u64, c: u64) {
    for _k in 0u64..n {
        let _ = need(c);
    }
}

// ---- NO over-rejection: must still verify ----

fn forward_call_outside_loop(n: u64, a: u64) {
    let _ = mk(a);
    let mut i = 0u64;
    while i < n {
        i = i + 1u64;
    }
    trust_vc::assert!(a == 7u64);
}

#[trust_vc::requires(n == 10u64)]
fn true_loop_invariant_post(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i >= 10u64);
}

fn met_requires_in_loop(n: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = need(20u64);
        i = i + 1u64;
    }
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_loop_body_call_ensures_leak_repro");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn assert_not_verified(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NOT verify (loop-body call-ensures must not leak past the loop), got Verified"
    );
}

fn assert_counterexample(func: &str) {
    let r = run(func);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{func} must be a Counterexample (NOT made vacuous / requires still checked), got: {r:?}"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (no over-rejection beyond dropping the in-loop ensures), got: {r:?}"
    );
}

// Direction (i): the leak is closed for every loop form. A loop-body call's
// `ensures` must NOT prove a post-loop assert / function postcondition, because
// the loop may run zero times.
#[test]
fn loop_body_call_ensures_leak_closed_while() {
    assert_not_verified("leak_while");
}
#[test]
fn loop_body_call_ensures_leak_closed_for() {
    assert_not_verified("leak_for");
}
#[test]
fn loop_body_call_ensures_leak_closed_bare_loop() {
    assert_not_verified("leak_bare");
}
#[test]
fn loop_body_call_ensures_leak_closed_nested() {
    assert_not_verified("leak_nested");
}
#[test]
fn loop_body_call_ensures_leak_closed_external_body() {
    assert_not_verified("leak_external_body");
}
#[test]
fn loop_body_call_ensures_leak_closed_postcondition() {
    assert_not_verified("leak_postcondition");
}

// Direction (ii) — THE DECISIVE iter-1 regression controls: in-loop OBLIGATIONS
// are NOT made vacuous. A genuinely-false assert inside a loop body, and a
// loop-body call with an UNMET precondition, must STILL be counterexamples.
#[test]
fn false_assert_in_while_stays_counterexample() {
    assert_counterexample("false_assert_in_while");
}
#[test]
fn false_assert_in_for_stays_counterexample() {
    assert_counterexample("false_assert_in_for");
}
#[test]
fn genuinely_false_assert_in_while_stays_counterexample() {
    assert_counterexample("genuinely_false_assert_in_while");
}
#[test]
fn unmet_requires_in_while_stays_counterexample() {
    assert_counterexample("unmet_requires_in_while");
}
#[test]
fn unmet_requires_in_for_stays_counterexample() {
    assert_counterexample("unmet_requires_in_for");
}

// Direction (iii): no over-rejection. A forward call OUTSIDE the loop still
// establishes its ensures; a true loop with an invariant-implied post-assert
// verifies; a loop-body call with a MET precondition verifies.
#[test]
fn forward_call_outside_loop_still_verifies() {
    assert_verified("forward_call_outside_loop");
}
#[test]
fn true_loop_invariant_post_still_verifies() {
    assert_verified("true_loop_invariant_post");
}
#[test]
fn met_requires_in_loop_still_verifies() {
    assert_verified("met_requires_in_loop");
}
