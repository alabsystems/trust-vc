// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 430 — code after an infinite loop is unreachable):
//! a bare `loop {}` that no `break` can leave (and that cannot `return`) marks
//! the code after it unreachable, so upstream `infinite_loop` / `loop_infinite2`
//! / `loop_infinite2y` (`assert(false)` after the loop) verify as they do in
//! Verus. The liars pin the fact's scope: it is forward-ordered (an `assert!`
//! BEFORE the loop does not see it), branch-guarded (a loop under `if c` yields
//! `!c` after the `if`, nothing more), never reaches the loop's own base case
//! or inductive step, and is not emitted when the body can `return`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ilu_{}_{}.rs", std::process::id(), tmp_id));
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
// upstream infinite_loop (Ok, unreachable warning).
#[trust_vc::ensures(true)]
pub fn infinite_loop() {
    loop {}
    trust_vc::assert!(false);
}

// The same with an invariant on the loop.
#[trust_vc::ensures(true)]
pub fn infinite_loop_with_invariant() {
    loop {
        trust_vc::invariant!(true);
    }
    trust_vc::assert!(false);
}

// upstream loop_infinite2 (Ok): the inner unlabeled break exits only the inner loop.
#[trust_vc::ensures(true)]
pub fn loop_infinite2() {
    'x: loop {
        'y: loop {
            break;
        }
    }
    trust_vc::assert!(false);
}

// upstream loop_infinite2y (Ok).
#[trust_vc::ensures(true)]
pub fn loop_infinite2y() {
    'x: loop {
        'y: loop {
            break 'y;
        }
    }
    trust_vc::assert!(false);
}

// upstream loop_infinite2x (FAILS): `break 'x` reaches the assertion.
#[trust_vc::ensures(true)]
pub fn loop_infinite2x() {
    'x: loop {
        'y: loop {
            break 'x;
        }
    }
    trust_vc::assert!(false);
}

// A function whose body never returns satisfies any postcondition (Verus Ok).
#[trust_vc::ensures(false)]
pub fn never_returns_satisfies_any_ensures() {
    let mut a: u64 = 5;
    loop {
        trust_vc::invariant!(a > 0u64);
        trust_vc::invariant!(a <= 1000u64);
        a = 1u64;
    }
}

// LIAR: the fact is forward-ordered — an assertion BEFORE the loop is checked.
#[trust_vc::ensures(true)]
pub fn assert_before_infinite_loop_is_checked(c: bool) {
    trust_vc::assert!(c);
    loop {}
}

// LIAR: the loop's own invariant is still established at entry.
#[trust_vc::ensures(true)]
pub fn infinite_loop_false_invariant_base_is_checked() {
    let mut x: u64 = 0;
    loop {
        trust_vc::invariant!(x == 100u64);
        x = x + 1u64;
    }
}

// LIAR: the loop's own invariant is still preserved.
#[trust_vc::ensures(true)]
pub fn infinite_loop_non_inductive_invariant_is_checked() {
    let mut x: u64 = 0;
    loop {
        trust_vc::invariant!(x == 0u64);
        x = 1u64;
    }
}

// LIAR: body arithmetic inside the infinite loop is still checked.
#[trust_vc::ensures(true)]
pub fn infinite_loop_body_overflow_is_checked(mut x: u64) {
    loop {
        trust_vc::invariant!(true);
        x = x + 1u64;
    }
}

// Branch-guarded: under `if c` the fact is exactly `!c` after the `if`.
#[trust_vc::ensures(true)]
pub fn conditional_infinite_loop_negates_condition(c: bool) {
    if c {
        loop {}
    }
    trust_vc::assert!(!c);
}

// LIAR: … and nothing more than `!c`.
#[trust_vc::ensures(true)]
pub fn conditional_infinite_loop_proves_only_negation(c: bool) {
    if c {
        loop {}
    }
    trust_vc::assert!(c);
}

// LIAR: a `return` inside the loop reaches the postcondition — no fact.
#[trust_vc::ensures(result == 6u64)]
pub fn loop_with_return_checks_the_return_path(c: bool) -> u64 {
    loop {
        if c {
            return 5u64;
        }
    }
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_not_verified(id: &str, func: &str) {
    if matches!(verify(id, func, SRC), VerifyResult::Verified) {
        panic!("{func}: expected a refutation or fail-closed, got Verified");
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn upstream_infinite_loop_verifies() {
    expect_verified("c1", "infinite_loop");
}

#[test]
fn infinite_loop_with_invariant_verifies() {
    expect_verified("c2", "infinite_loop_with_invariant");
}

#[test]
fn upstream_loop_infinite2_verifies() {
    expect_verified("c3", "loop_infinite2");
}

#[test]
fn upstream_loop_infinite2y_verifies() {
    expect_verified("c4", "loop_infinite2y");
}

#[test]
fn upstream_loop_infinite2x_is_rejected() {
    expect_counterexample("l1", "loop_infinite2x");
}

#[test]
fn never_returning_body_satisfies_any_ensures() {
    expect_verified("c5", "never_returns_satisfies_any_ensures");
}

#[test]
fn liar_assert_before_infinite_loop_is_checked() {
    expect_counterexample("l2", "assert_before_infinite_loop_is_checked");
}

#[test]
fn liar_infinite_loop_false_invariant_base_is_checked() {
    expect_counterexample("l3", "infinite_loop_false_invariant_base_is_checked");
}

#[test]
fn liar_infinite_loop_non_inductive_invariant_is_checked() {
    expect_counterexample("l4", "infinite_loop_non_inductive_invariant_is_checked");
}

#[test]
fn liar_infinite_loop_body_overflow_is_checked() {
    expect_counterexample("l5", "infinite_loop_body_overflow_is_checked");
}

#[test]
fn conditional_infinite_loop_negates_condition_verifies() {
    expect_verified("c6", "conditional_infinite_loop_negates_condition");
}

#[test]
fn liar_conditional_infinite_loop_proves_only_negation() {
    expect_counterexample("l6", "conditional_infinite_loop_proves_only_negation");
}

#[test]
fn liar_loop_with_return_checks_the_return_path() {
    expect_not_verified("l7", "loop_with_return_checks_the_return_path");
}
