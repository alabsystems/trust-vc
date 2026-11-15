// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (audit rows 428/429 — invariant scope across loops,
//! 2026-09-11). Two measured false-verifies in functions with TWO loops:
//!
//! 1. The typed lane assumed every PREVIOUSLY VERIFIED invariant of the
//!    function at the pre-state of a later inductive step — so an earlier
//!    loop's invariant `x == 10` (true at that loop's heads) was assumed at a
//!    later loop's head where `x` has moved, and a false invariant `x <= 11`
//!    on `while x < 100 { x = x + 1 }` was "preserved" (`assert!(false)` after
//!    it VERIFIED). Inductive steps, measures, exit checks and `loop_ensures`
//!    now assume exactly the invariants of THEIR OWN loop (all of them, as
//!    Verus does), keyed by a per-loop group the extractor registers.
//! 2. With one declared symbol per variable, the post-loop facts of two loops
//!    that both carry invariants and both modify the same variable land on the
//!    SAME symbol (`i == 10` from the first, `i == 20` from the second — a
//!    contradiction that proved anything after the second loop). The extractor
//!    now FAILS CLOSED on that shape with a precise message; the exit-symbol
//!    model that would verify it is the recorded follow-up.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lis_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
// LIAR (1): the first loop's invariant `x == 10` must not reach the second
// loop's inductive step — `x <= 11` is not preserved by `x = x + 1` under
// `x < 100`.
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(true)]
pub fn prior_loop_invariant_leaks_into_later_step(mut x: u64) {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == 10u64);
        i = i + 1u64;
    }
    while x < 100u64 {
        trust_vc::invariant!(x <= 11u64);
        x = x + 1u64;
    }
    trust_vc::assert!(false);
}

// CONTROL (1): the same program with the invariant that IS preserved.
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(true)]
pub fn prior_loop_invariant_control(mut x: u64) {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == 10u64);
        i = i + 1u64;
    }
    while x < 100u64 {
        trust_vc::invariant!(x <= 100u64);
        x = x + 1u64;
    }
    trust_vc::assert!(x == 100u64);
    trust_vc::assert!(i == 10u64);
}

// LIAR (2): two loops with invariants over the same counter — the post-loop
// facts would share one symbol; the extractor fails closed instead of
// proving `i <= 10` (or anything) after the second loop.
#[trust_vc::ensures(true)]
pub fn sequential_loops_shared_counter(  ) {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    while i < 20u64 {
        trust_vc::invariant!(i <= 20u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i <= 10u64);
}

// LIAR (2): … and `assert!(false)` after the pair.
#[trust_vc::ensures(true)]
pub fn sequential_loops_shared_counter_false() {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    while i < 20u64 {
        trust_vc::invariant!(i <= 11u64);
        i = i + 1u64;
    }
    trust_vc::assert!(false);
}

// CONTROL (2): two loops with invariants over DIFFERENT counters keep both
// exit values.
#[trust_vc::ensures(true)]
pub fn sequential_loops_disjoint_counters() {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    while j < 5u64 {
        trust_vc::invariant!(j <= 5u64);
        j = j + 1u64;
    }
    trust_vc::assert!(i == 10u64);
    trust_vc::assert!(j == 5u64);
}

// CONTROL (2): an invariant loop followed by a plain loop over the same
// counter: the second loop freshens the counter, so only its exit fact holds.
#[trust_vc::ensures(true)]
pub fn invariant_loop_then_plain_loop() {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    while i < 20u64 {
        i = i + 1u64;
    }
    trust_vc::assert!(i >= 20u64);
}

// LIAR: … and the first loop's exit value is gone after the second.
#[trust_vc::ensures(true)]
pub fn invariant_loop_then_plain_loop_liar() {
    let mut i: u64 = 0;
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    while i < 20u64 {
        i = i + 1u64;
    }
    trust_vc::assert!(i == 10u64);
}

// CONTROL: nested loops share modified vars by construction (the outer set
// contains the inner's) and are NOT the sequential shape — still verified.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn nested_loops_are_not_sequential(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
        }
        trust_vc::assert!(j == 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == n);
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_fail_closed(id: &str, func: &str, needle: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Error { message } if message.contains(needle) => {}
        other => {
            panic!("{func}: expected a fail-closed Error mentioning {needle:?}, got {other:?}")
        }
    }
}

#[test]
fn liar_prior_loop_invariant_leaks_into_later_step_is_rejected() {
    expect_counterexample("l1", "prior_loop_invariant_leaks_into_later_step");
}

#[test]
fn control_prior_loop_invariant_control_verifies() {
    expect_verified("c1", "prior_loop_invariant_control");
}

#[test]
fn liar_sequential_loops_shared_counter_fails_closed() {
    expect_fail_closed("l2", "sequential_loops_shared_counter", "two loops");
}

#[test]
fn liar_sequential_loops_shared_counter_false_fails_closed() {
    expect_fail_closed("l3", "sequential_loops_shared_counter_false", "two loops");
}

#[test]
fn control_sequential_loops_disjoint_counters_verifies() {
    expect_verified("c2", "sequential_loops_disjoint_counters");
}

#[test]
fn control_invariant_loop_then_plain_loop_verifies() {
    expect_verified("c3", "invariant_loop_then_plain_loop");
}

#[test]
fn liar_invariant_loop_then_plain_loop_is_rejected() {
    expect_counterexample("l4", "invariant_loop_then_plain_loop_liar");
}

#[test]
fn control_nested_loops_are_not_sequential_verifies() {
    expect_verified("c4", "nested_loops_are_not_sequential");
}
