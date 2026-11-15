// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 430/431 — nested loops that modify state AND
//! `break`, 2026-09-10): a nested loop whose body is exact (its break sites are
//! checked exit sites) is summarized for the enclosing transition from the
//! predicates that hold at EVERY exit — its regular invariants and
//! `loop_ensures` — while `invariant_except_break` and the negated guard are
//! NOT assumed (a break leaves with the guard still true). The liars pin both
//! exclusions and the liveness of the inner loop's own site checks.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nbls_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL: a search-style inner loop with a break; the outer invariant over
// `j` is preserved through the inner regular invariant `j <= 10`.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn breaking_inner_loop_keeps_outer_invariant(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 10u64);
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
        i = i + 1u64;
    }
    trust_vc::assert!(j <= 10u64);
}

// LIAR: the inner regular invariant says `j <= 10`, not `j <= 4` (the break
// leaves with `j == 5`).
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn breaking_inner_loop_outer_invariant_too_strong(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 4u64);
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
        i = i + 1u64;
    }
}

// LIAR: `invariant_except_break` is NOT an exit fact — after the inner loop
// `j < 5` is false on the break path (`j == 5`).
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn except_break_invariant_is_not_an_exit_fact(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 10u64);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant_except_break!(j < 5u64);
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
        trust_vc::assert!(j < 5u64);
        i = i + 1u64;
    }
}

// LIAR: the negated guard is NOT an exit fact — the break leaves with `j < 10`.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn negated_guard_is_not_an_exit_fact_after_break(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 10u64);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
        trust_vc::assert!(j >= 10u64);
        i = i + 1u64;
    }
}

// CONTROL: `loop_ensures` IS an exit fact (checked at the break site and at
// the normal exit).
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn loop_ensures_is_an_exit_fact(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            trust_vc::loop_ensures!(j == 5u64 || j == 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
        trust_vc::assert!(j == 5u64 || j == 10u64);
        i = i + 1u64;
    }
}

// LIAR: a false `loop_ensures` is refuted at the inner break site itself.
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn false_inner_loop_ensures_is_refuted(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        j = 0u64;
        while j < 10u64 {
            trust_vc::invariant!(j <= 10u64);
            trust_vc::loop_ensures!(j == 10u64);
            j = j + 1u64;
            if j == 5u64 {
                break;
            }
        }
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
fn control_breaking_inner_loop_keeps_outer_invariant() {
    expect_verified("c1", "breaking_inner_loop_keeps_outer_invariant");
}

#[test]
fn liar_breaking_inner_loop_outer_invariant_too_strong() {
    expect_counterexample("l1", "breaking_inner_loop_outer_invariant_too_strong");
}

#[test]
fn liar_except_break_invariant_is_not_an_exit_fact() {
    expect_counterexample("l2", "except_break_invariant_is_not_an_exit_fact");
}

#[test]
fn liar_negated_guard_is_not_an_exit_fact_after_break() {
    expect_counterexample("l3", "negated_guard_is_not_an_exit_fact_after_break");
}

#[test]
fn control_loop_ensures_is_an_exit_fact() {
    expect_verified("c2", "loop_ensures_is_an_exit_fact");
}

#[test]
fn liar_false_inner_loop_ensures_is_refuted() {
    expect_counterexample("l4", "false_inner_loop_ensures_is_refuted");
}
