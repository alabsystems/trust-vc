// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 433 — range `for` loops, 2026-09-10): the desugar
//! now auto-injects the UPPER bound (`LO <= HI ==> i <= HI`, `<= HI + 1` for
//! `..=`) beside the lower one, so an accumulator invariant alone pins the
//! post-loop value (`i == HI`, the Verus range iterator's `cur == end`), and it
//! accepts any body that does not `continue` the loop or reassign the counter
//! or the bounds (the `while` it produces takes the exact lane when flat and
//! the havoc lane otherwise). Upstream for_loop1::test_loop_peek and
//! for_loop2::test_loop verify with only their accumulator invariants.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_frb_{}_{}.rs", std::process::id(), tmp_id));
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
// upstream for_loop1::test_loop_peek (Ok): only the accumulator invariant.
#[trust_vc::ensures(true)]
pub fn for_loop1_test_loop_peek() {
    let mut n: u64 = 0;
    for x in 0u64..10u64 {
        trust_vc::invariant!(n == x * 3u64);
        trust_vc::assert!(x < 10u64);
        n = n + 3u64;
    }
    trust_vc::assert!(n == 30u64);
}

// LIAR: the post-loop value is 30, not 33.
#[trust_vc::ensures(true)]
pub fn for_loop1_wrong_post_loop_value() {
    let mut n: u64 = 0;
    for x in 0u64..10u64 {
        trust_vc::invariant!(n == x * 3u64);
        n = n + 3u64;
    }
    trust_vc::assert!(n == 33u64);
}

// An inclusive range: `0..=9` also ends at 30.
#[trust_vc::ensures(true)]
pub fn inclusive_range_accumulator() {
    let mut n: u64 = 0;
    for x in 0u64..=9u64 {
        trust_vc::invariant!(n == x * 3u64);
        n = n + 3u64;
    }
    trust_vc::assert!(n == 30u64);
}

// A variable upper bound: the exit fact `x == m` reaches the post-loop assertion.
#[trust_vc::requires(m < 100u64)]
#[trust_vc::ensures(true)]
pub fn variable_upper_bound(m: u64) {
    let mut n: u64 = 0;
    for x in 0u64..m {
        trust_vc::invariant!(n == x);
        n = n + 1u64;
    }
    trust_vc::assert!(n == m);
}

// upstream for_loop2::test_loop (Ok): the bound is a `let`, unchanged by the body.
#[trust_vc::ensures(true)]
pub fn for_loop2_test_loop() {
    let mut n: u64 = 0;
    let end: u64 = 10;
    for x in 0u64..end {
        trust_vc::invariant!(n == x * 3u64);
        trust_vc::invariant!(end == 10u64);
        trust_vc::assert!(x < 10u64);
        n = n + 3u64;
    }
    trust_vc::assert!(n == 30u64);
}

// A NON-flat body (an `if`) no longer fails closed: the produced `while` takes
// the havoc lane, so an unmodified-state fact survives and the counter's bound
// invariants stay inductive (its `i = i + 1` is a single top-level write).
#[trust_vc::requires(limit == 7u64)]
#[trust_vc::ensures(true)]
pub fn non_flat_body_verifies(limit: u64, c: bool) {
    let mut hits: u64 = 0;
    for i in 0u64..limit {
        trust_vc::invariant!(limit == 7u64);
        if c {
            hits = 1u64;
        }
    }
    trust_vc::assert!(limit == 7u64);
}

// LIAR: … but a var written in a branch is havoc'd, not assumed.
#[trust_vc::requires(limit == 7u64)]
#[trust_vc::ensures(true)]
pub fn non_flat_body_havocs_written_var(limit: u64, c: bool) {
    let mut hits: u64 = 0;
    for i in 0u64..limit {
        trust_vc::invariant!(limit == 7u64);
        if c {
            hits = 1u64;
        }
    }
    trust_vc::assert!(hits == 0u64);
}

// LIAR (SOUNDNESS, pre-existing hole surfaced by the relaxed desugar): an
// addition on a branch whose condition reads the loop counter — `x + 100` is
// unbounded at the loop head and overflows on the second iteration. The
// branch condition used to be rendered over the bare counter while the site
// used the head symbol, and the "inconsistent" obligation was deferred, i.e.
// never checked.
#[trust_vc::requires(x == 18446744073709551465u64)]
#[trust_vc::ensures(true)]
pub fn branch_conditional_overflow_in_for_body(mut x: u64) {
    for k in 0u64..3u64 {
        trust_vc::invariant!(true);
        if k < 3u64 {
            x = x + 100u64;
        }
    }
}

// The same shape as a plain `while` (the counter incremented at the end).
#[trust_vc::requires(x == 18446744073709551465u64)]
#[trust_vc::ensures(true)]
pub fn branch_conditional_overflow_in_while_body(mut x: u64) {
    let mut k: u64 = 0;
    while k < 3u64 {
        trust_vc::invariant!(true);
        if k < 3u64 {
            x = x + 100u64;
        }
        k = k + 1u64;
    }
}

// CONTROL: a safe addition on the same kind of branch (its operand is a var
// the loop never modifies) still verifies — the head-rendered guard does not
// over-reject.
#[trust_vc::requires(c < 1000u64)]
#[trust_vc::ensures(true)]
pub fn branch_conditional_bounded_addition_verifies(c: u64) {
    let mut y: u64 = 0;
    for k in 0u64..3u64 {
        trust_vc::invariant!(true);
        if k < 3u64 {
            y = c + 100u64;
        }
    }
    trust_vc::assert!(c < 1000u64);
}

// LIAR: a `continue` would skip the appended increment — the loop is not
// desugared and stays fail-closed (never a false Verified).
#[trust_vc::ensures(true)]
pub fn continue_body_is_not_desugared() {
    let mut n: u64 = 0;
    for x in 0u64..10u64 {
        trust_vc::invariant!(n <= x);
        if x == 3u64 {
            continue;
        }
        n = n + 1u64;
    }
    trust_vc::assert!(n == 9u64);
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

fn expect_not_verified(id: &str, func: &str) {
    if matches!(verify(id, func, SRC), VerifyResult::Verified) {
        panic!("{func}: expected a refutation or fail-closed, got Verified");
    }
}

#[test]
fn upstream_for_loop1_test_loop_peek_verifies() {
    expect_verified("c1", "for_loop1_test_loop_peek");
}

#[test]
fn liar_for_loop1_wrong_post_loop_value() {
    expect_counterexample("l1", "for_loop1_wrong_post_loop_value");
}

#[test]
fn inclusive_range_accumulator_verifies() {
    expect_verified("c2", "inclusive_range_accumulator");
}

#[test]
fn variable_upper_bound_verifies() {
    expect_verified("c3", "variable_upper_bound");
}

#[test]
fn upstream_for_loop2_test_loop_verifies() {
    expect_verified("c4", "for_loop2_test_loop");
}

#[test]
fn non_flat_body_verifies() {
    expect_verified("c5", "non_flat_body_verifies");
}

#[test]
fn liar_non_flat_body_havocs_written_var() {
    expect_counterexample("l2", "non_flat_body_havocs_written_var");
}

#[test]
fn liar_branch_conditional_overflow_in_for_body_is_rejected() {
    expect_counterexample("l4", "branch_conditional_overflow_in_for_body");
}

#[test]
fn liar_branch_conditional_overflow_in_while_body_is_rejected() {
    expect_counterexample("l5", "branch_conditional_overflow_in_while_body");
}

#[test]
fn control_branch_conditional_bounded_addition_verifies() {
    expect_verified("c6", "branch_conditional_bounded_addition_verifies");
}

#[test]
fn liar_continue_body_is_not_desugared() {
    expect_not_verified("l3", "continue_body_is_not_desugared");
}
