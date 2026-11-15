// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS + CAPABILITY PIN (audit rows 430/431 — nested loops):
//!
//! * SOUNDNESS: a NESTED loop's own spec predicates (`invariant!`,
//!   `invariant_except_break!`, `loop_ensures!`) are checked at the enclosing
//!   loop's ARBITRARY head — over the enclosing loop's fresh head symbols and
//!   under its guard ∧ invariants — exactly like a body `assert!`. Before, they
//!   were rendered over the BARE names, so an outer-modified variable kept its
//!   function-entry (`requires`) facts and an inner invariant that holds only on
//!   the FIRST outer iteration verified (measured 2026-09-10).
//! * CAPABILITY: an inner loop that assigns nothing (spec macros, break/continue
//!   sites targeting itself, further such loops) is admitted to the enclosing
//!   body's exact-transition lane — upstream `loop2_ok` / `loop2_ok_y` verify,
//!   `loop2_fail1` / `loop2_fail2` are refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nlhf_{}_{}.rs", std::process::id(), tmp_id));
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
// LIAR: the inner invariant holds on the FIRST outer iteration only (`flag`
// starts true, the body toggles it). Verus: "invariant not satisfied at loop
// entry" on the second outer iteration.
#[trust_vc::requires(flag)]
#[trust_vc::ensures(true)]
pub fn inner_invariant_true_only_at_first_outer_iteration(mut flag: bool, b: bool) {
    loop {
        trust_vc::invariant!(true);
        flag = !flag;
        loop {
            trust_vc::invariant!(!flag);
            break;
        }
        if b {
            break;
        }
    }
}

// LIAR: same shape through a `loop_ensures!` on the inner loop.
#[trust_vc::requires(flag)]
#[trust_vc::ensures(true)]
pub fn inner_loop_ensures_true_only_at_first_outer_iteration(mut flag: bool, b: bool) {
    loop {
        trust_vc::invariant!(true);
        flag = !flag;
        loop {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(!flag);
            break;
        }
        if b {
            break;
        }
    }
}

// LIAR: the inner invariant reads the outer-modified counter through the
// function-entry fact (`i == 0`) — false from the second outer head on.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn inner_invariant_reads_stale_entry_counter(mut i: u64, b: bool) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        if i < 10u64 {
            i = i + 1u64;
        }
        loop {
            trust_vc::invariant!(i == 1u64);
            break;
        }
        if b {
            break;
        }
    }
}

// upstream loop2_ok (Ok).
#[trust_vc::ensures(true)]
pub fn loop2_ok(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }
    trust_vc::assert!(i == 0i8);
}

// upstream loop2_ok_y (Ok): the inner break is labeled with the INNER label.
#[trust_vc::ensures(true)]
pub fn loop2_ok_y(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break 'y;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }
    trust_vc::assert!(i == 0i8);
}

// upstream loop2_fail1 (FAILS): `break 'x` leaves the outer loop with i == 1.
#[trust_vc::ensures(true)]
pub fn loop2_fail1(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break 'x;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }
    trust_vc::assert!(i == 0i8);
}

// upstream loop2_fail2 (FAILS): the outer break site is reached with i == 1.
#[trust_vc::ensures(true)]
pub fn loop2_fail2(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break;
        }
        if b {
            break;
        }
        i = i - 1i8;
    }
    trust_vc::assert!(i == 0i8);
}

// CONTROL (no over-rejection): an inner invariant over UNMODIFIED state still
// verifies from the function's `requires`, and the outer fact survives.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn inner_invariant_over_unmodified_state_verifies(mut i: u64, limit: u64, b: bool) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        i = 1u64;
        loop {
            trust_vc::invariant!(limit == 10u64);
            break;
        }
        if b {
            break;
        }
    }
    trust_vc::assert!(limit == 10u64);
}

// CONTROL: a guarded inner `while` (side-effect-free guard, body exits itself)
// nested in a `while` counter loop; the inner invariant follows from the outer
// head state, and the outer normal-exit fact is unaffected by the inner break.
#[trust_vc::ensures(true)]
pub fn while_in_while_noop_inner_verifies(n: u64) {
    let mut i: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        i = i + 1u64;
        'y: while i > 0u64 {
            trust_vc::invariant!(i >= 1u64);
            break 'y;
        }
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

#[test]
fn liar_inner_invariant_true_only_at_first_outer_iteration_is_rejected() {
    expect_counterexample("l1", "inner_invariant_true_only_at_first_outer_iteration");
}

#[test]
fn liar_inner_loop_ensures_true_only_at_first_outer_iteration_is_rejected() {
    expect_counterexample(
        "l2",
        "inner_loop_ensures_true_only_at_first_outer_iteration",
    );
}

#[test]
fn liar_inner_invariant_reads_stale_entry_counter_is_rejected() {
    expect_counterexample("l3", "inner_invariant_reads_stale_entry_counter");
}

#[test]
fn upstream_loop2_ok_verifies() {
    expect_verified("c1", "loop2_ok");
}

#[test]
fn upstream_loop2_ok_y_verifies() {
    expect_verified("c2", "loop2_ok_y");
}

#[test]
fn upstream_loop2_fail1_is_rejected() {
    expect_counterexample("l4", "loop2_fail1");
}

#[test]
fn upstream_loop2_fail2_is_rejected() {
    expect_counterexample("l5", "loop2_fail2");
}

#[test]
fn control_inner_invariant_over_unmodified_state_verifies() {
    expect_verified("c3", "inner_invariant_over_unmodified_state_verifies");
}

#[test]
fn control_while_in_while_noop_inner_verifies() {
    expect_verified("c4", "while_in_while_noop_inner_verifies");
}
