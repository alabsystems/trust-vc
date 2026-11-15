// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS + CAPABILITY PIN (rows 428/429 — a DECLARED var assigned right
//! before a loop, 2026-09-11): `j = 0; while j < 10 { … }` on a `mut` param
//! (or a var an enclosing loop already declared) used to render the `while`
//! guard from `j`'s pre-loop scoped value — `0 < 10` — so the inductive step
//! lost its guard and the normal-exit fact became `!(0 < 10)` = false (a
//! `requires(j == 0)` twin then proved `assert!(false)`), while the base case
//! never saw the assignment at all (an over-rejection of the plain counter
//! loop). The pre-loop value is now captured as the base-case entry binding and
//! the scoped value is cleared before the guard renders, exactly as for a
//! `let mut` counter.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_padv_{}_{}.rs", std::process::id(), tmp_id));
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
// LIAR (SOUNDNESS): the normal-exit fact must be `!(j < 10)`, never `!(0 < 10)`.
// The body's step is inductive WITHOUT the guard (the increment is guarded),
// so nothing else masks a false exit fact — this loop terminates at 10 and the
// assertion after it is reachable.
#[trust_vc::requires(j == 0u64)]
#[trust_vc::ensures(true)]
pub fn redundant_preloop_assignment_false_exit_fact(mut j: u64) {
    j = 0u64;
    while j < 10u64 {
        trust_vc::invariant!(j <= 10u64);
        if j < 10u64 {
            j = j + 1u64;
        }
    }
    trust_vc::assert!(false);
}

// LIAR (SOUNDNESS, 2026-09-11): the pre-loop value `j = 0` disagrees with the
// `requires` — the base case must see `j == 0` (the invariant is false there),
// not a contradiction between the entry fact and the entry binding.
#[trust_vc::requires(j == 5u64)]
#[trust_vc::ensures(true)]
pub fn preloop_assignment_contradicts_requires_liar(mut j: u64) {
    j = 0u64;
    while j < 10u64 {
        trust_vc::invariant!(j >= 5u64);
        j = j + 1u64;
    }
}

// LIAR (SOUNDNESS, 2026-09-11): a pre-loop value that reads the var itself
// (`x = x + 1`) must bind the head value to the ENTRY value plus one, not to
// itself plus one.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn preloop_self_referential_assignment_liar(mut x: u64) {
    x = x + 1u64;
    while x < 10u64 {
        trust_vc::invariant!(x >= 5u64);
        x = x + 1u64;
    }
}

// CONTROL: … and the entry value `x == 1` is known to the base case.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn preloop_self_referential_assignment_control(mut x: u64) {
    x = x + 1u64;
    while x < 10u64 {
        trust_vc::invariant!(x >= 1u64);
        trust_vc::invariant!(x <= 10u64);
        x = x + 1u64;
    }
    trust_vc::assert!(x == 10u64);
}

// LIAR: `assert!(false)` after a terminating counter loop.
#[trust_vc::ensures(true)]
pub fn preloop_assignment_then_while_liar(mut j: u64) {
    j = 0u64;
    while j < 10u64 {
        trust_vc::invariant!(j <= 10u64);
        j = j + 1u64;
    }
    trust_vc::assert!(false);
}

// CONTROL: the pre-loop assignment establishes the base case and the exit
// value is known.
#[trust_vc::ensures(true)]
pub fn preloop_assignment_then_while_exit_value(mut j: u64) {
    j = 0u64;
    while j < 10u64 {
        trust_vc::invariant!(j <= 10u64);
        j = j + 1u64;
    }
    trust_vc::assert!(j == 10u64);
}

// LIAR: the pre-loop value is the ENTRY value only — not a post-loop fact.
#[trust_vc::ensures(true)]
pub fn preloop_assignment_is_not_a_post_loop_fact(mut j: u64) {
    j = 0u64;
    while j < 10u64 {
        trust_vc::invariant!(j <= 10u64);
        j = j + 1u64;
    }
    trust_vc::assert!(j == 0u64);
}

// CONTROL (nested): a var reset in the outer body before an inner loop keeps
// the inner guard over the var, so the inner exit value is known in the body.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn nested_reset_then_while(n: u64) {
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
}

// LIAR (nested): … and `j == 0` after the inner loop is false.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn nested_reset_then_while_liar(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
        }
        trust_vc::assert!(j == 0u64);
        i = i + 1u64;
    }
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

#[test]
fn liar_redundant_preloop_assignment_false_exit_fact_is_rejected() {
    expect_counterexample("l1", "redundant_preloop_assignment_false_exit_fact");
}

#[test]
fn liar_preloop_assignment_contradicts_requires_is_rejected() {
    expect_counterexample("l5", "preloop_assignment_contradicts_requires_liar");
}

#[test]
fn liar_preloop_self_referential_assignment_is_rejected() {
    expect_counterexample("l6", "preloop_self_referential_assignment_liar");
}

#[test]
fn control_preloop_self_referential_assignment_verifies() {
    expect_verified("c3", "preloop_self_referential_assignment_control");
}

#[test]
fn liar_preloop_assignment_then_while_is_rejected() {
    expect_counterexample("l2", "preloop_assignment_then_while_liar");
}

#[test]
fn control_preloop_assignment_then_while_exit_value_verifies() {
    expect_verified("c1", "preloop_assignment_then_while_exit_value");
}

#[test]
fn liar_preloop_assignment_is_not_a_post_loop_fact() {
    expect_counterexample("l3", "preloop_assignment_is_not_a_post_loop_fact");
}

#[test]
fn control_nested_reset_then_while_verifies() {
    expect_verified("c2", "nested_reset_then_while");
}

#[test]
fn liar_nested_reset_then_while_is_rejected() {
    expect_counterexample("l4", "nested_reset_then_while_liar");
}
