// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 430/431/433 — a nested range `for` inside an
//! exact loop body, 2026-09-10): the range-`for` desugar emits
//! `{ let mut j = LO; while j < HI { … } }`; that block is now visited with its
//! own scope and its `while` is summarized for the enclosing transition, with
//! the block-local counter given an exit symbol too, so the exit facts
//! (`LO <= j`, the user's invariants, `!(j < HI)`, the snapshot alias equations)
//! survive the block. A
//! summation loop nested in a counter loop verifies; the liars pin that the
//! facts are exactly the inner spec and that nothing stale survives.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nfs_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL: a nested summation `for` keeps the outer invariant `total == 3 * i`
// through the inner exit facts (`total == t0 + j`, `j == 3`).
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_summation(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i);
        let t0 = total;
        for j in 0u64..3u64 {
            trust_vc::invariant!(j <= 3u64);
            trust_vc::invariant!(total == t0 + j);
            total = total + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(total == 3u64 * n);
}

// LIAR: an outer invariant the inner exit facts do not support.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_summation_wrong_outer_invariant(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i + 1u64);
        let t0 = total;
        for j in 0u64..3u64 {
            trust_vc::invariant!(j <= 3u64);
            trust_vc::invariant!(total == t0 + j);
            total = total + 1u64;
        }
        i = i + 1u64;
    }
}

// LIAR: a wrong post-loop value.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_summation_wrong_post_loop_value(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i);
        let t0 = total;
        for j in 0u64..3u64 {
            trust_vc::invariant!(j <= 3u64);
            trust_vc::invariant!(total == t0 + j);
            total = total + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(total == 3u64 * n + 1u64);
}

// LIAR: without the inner invariant nothing relates `total` to the counter, so
// the outer invariant is NOT preserved (the summary assumes only the inner
// loop's own spec).
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_summation_without_inner_invariant(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i);
        for _j in 0u64..3u64 {
            total = total + 1u64;
        }
        i = i + 1u64;
    }
}

// CONTROL: a body assertion after the nested `for` sees its exit facts.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_body_assertion_sees_exit_facts(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i);
        let t0 = total;
        for j in 0u64..3u64 {
            trust_vc::invariant!(j <= 3u64);
            trust_vc::invariant!(total == t0 + j);
            total = total + 1u64;
        }
        trust_vc::assert!(total == t0 + 3u64);
        i = i + 1u64;
    }
}

// LIAR: … and not a stale value.
#[trust_vc::requires(n < 1000u64)]
#[trust_vc::ensures(true)]
pub fn nested_for_body_assertion_not_stale(n: u64) {
    let mut i: u64 = 0;
    let mut total: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total == 3u64 * i);
        let t0 = total;
        for j in 0u64..3u64 {
            trust_vc::invariant!(j <= 3u64);
            trust_vc::invariant!(total == t0 + j);
            total = total + 1u64;
        }
        trust_vc::assert!(total == t0);
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
fn control_nested_for_summation_verifies() {
    expect_verified("c1", "nested_for_summation");
}

#[test]
fn liar_nested_for_summation_wrong_outer_invariant() {
    expect_counterexample("l1", "nested_for_summation_wrong_outer_invariant");
}

#[test]
fn liar_nested_for_summation_wrong_post_loop_value() {
    expect_counterexample("l2", "nested_for_summation_wrong_post_loop_value");
}

#[test]
fn liar_nested_for_summation_without_inner_invariant() {
    expect_counterexample("l3", "nested_for_summation_without_inner_invariant");
}

#[test]
fn control_nested_for_body_assertion_sees_exit_facts() {
    expect_verified("c2", "nested_for_body_assertion_sees_exit_facts");
}

#[test]
fn liar_nested_for_body_assertion_not_stale() {
    expect_counterexample("l4", "nested_for_body_assertion_not_stale");
}
