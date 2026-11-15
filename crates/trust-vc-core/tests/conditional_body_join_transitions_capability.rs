// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 428/430 — conditional loop bodies in the exact
//! lane, 2026-09-10): an `if`/`else` whose branches are flat scalar assignments
//! and spec macros (no exits, no lets, no loops) joins each branch-assigned
//! scalar into a CONDITIONAL value `if c { then } else { else }` instead of
//! havocing it, so the body stays in the exact-transition lane and the inductive
//! step sees both paths. Straight-line joins gain the same precision. The liars
//! pin that only what both branches establish is assumed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cbjt_{}_{}.rs", std::process::id(), tmp_id));
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
// The former gate fixture: `i <= n` IS preserved on both paths.
#[trust_vc::requires(i <= n)]
#[trust_vc::ensures(true)]
pub fn cond_body(mut i: u64, n: u64, c: bool) {
    while i < n {
        trust_vc::invariant!(i <= n);
        if c {
            i = i + 1u64;
        }
    }
}

// A conditional accumulator: `count <= i` holds whether or not the branch runs.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn conditional_accumulator(n: u64, c: bool) {
    let mut i: u64 = 0;
    let mut count: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(count <= i);
        if c {
            count = count + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(count <= n);
}

// LIAR: the branch may not run, so `count == i` is not preserved.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn conditional_accumulator_liar(n: u64, c: bool) {
    let mut i: u64 = 0;
    let mut count: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(count == i);
        if c {
            count = count + 1u64;
        }
        i = i + 1u64;
    }
}

// An if/else assigning different values keeps both.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn if_else_join_in_loop(n: u64, c: bool) {
    let mut i: u64 = 0;
    let mut x: u64 = 1;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(x == 1u64 || x == 2u64);
        if c {
            x = 1u64;
        } else {
            x = 2u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(x == 1u64 || x == 2u64);
}

// LIAR: `x == 1` is not what both branches establish.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn if_else_join_in_loop_liar(n: u64, c: bool) {
    let mut i: u64 = 0;
    let mut x: u64 = 1;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(x == 1u64);
        if c {
            x = 1u64;
        } else {
            x = 2u64;
        }
        i = i + 1u64;
    }
}

// Straight-line: the join keeps both branch values.
#[trust_vc::ensures(true)]
pub fn straight_line_join(c: bool) {
    let mut x: u64 = 0;
    if c {
        x = 5u64;
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// LIAR (straight-line).
#[trust_vc::ensures(true)]
pub fn straight_line_join_liar(c: bool) {
    let mut x: u64 = 0;
    if c {
        x = 5u64;
    }
    trust_vc::assert!(x == 5u64);
}

// A later assignment reads the JOINED value, not a stale one: after the `if`,
// `y = x + 1` is `6` or `1`.
#[trust_vc::ensures(true)]
pub fn dependent_assignment_after_join(c: bool) {
    let mut x: u64 = 0;
    if c {
        x = 5u64;
    }
    let y = x + 1u64;
    trust_vc::assert!(y == 6u64 || y == 1u64);
}

// LIAR: … and `y == 1` alone is not implied.
#[trust_vc::ensures(true)]
pub fn dependent_assignment_after_join_liar(c: bool) {
    let mut x: u64 = 0;
    if c {
        x = 5u64;
    }
    let y = x + 1u64;
    trust_vc::assert!(y == 1u64);
}

// A branch that `break`s stays a break site (exact lane, exit checks), not a
// join — the upstream example_loop_break shape.
#[trust_vc::ensures(true)]
pub fn break_branch_is_not_joined() {
    let mut i: u64 = 0;
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::loop_ensures!(i == 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i == 10u64);
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
fn control_cond_body_verifies() {
    expect_verified("c1", "cond_body");
}

#[test]
fn control_conditional_accumulator_verifies() {
    expect_verified("c2", "conditional_accumulator");
}

#[test]
fn liar_conditional_accumulator_is_rejected() {
    expect_counterexample("l1", "conditional_accumulator_liar");
}

#[test]
fn control_if_else_join_in_loop_verifies() {
    expect_verified("c3", "if_else_join_in_loop");
}

#[test]
fn liar_if_else_join_in_loop_is_rejected() {
    expect_counterexample("l2", "if_else_join_in_loop_liar");
}

#[test]
fn control_straight_line_join_verifies() {
    expect_verified("c4", "straight_line_join");
}

#[test]
fn liar_straight_line_join_is_rejected() {
    expect_counterexample("l3", "straight_line_join_liar");
}

#[test]
fn control_dependent_assignment_after_join_verifies() {
    expect_verified("c5", "dependent_assignment_after_join");
}

#[test]
fn liar_dependent_assignment_after_join_is_rejected() {
    expect_counterexample("l4", "dependent_assignment_after_join_liar");
}

#[test]
fn control_break_branch_is_not_joined() {
    expect_verified("c6", "break_branch_is_not_joined");
}
