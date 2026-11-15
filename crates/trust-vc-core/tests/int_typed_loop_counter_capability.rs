// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 430 — `int` / `nat` loop counters, upstream
//! basic_loop): a mathematical-integer `let mut` local modified in a loop is
//! declared and framed like a fixed-width counter (entry binding at the base
//! case, havoc in the inductive step, exit-site checks, post-loop facts). Before
//! 2026-09-10 every invariant over such a counter failed to lower ("unresolved
//! variable"). The liars pin that nothing is assumed: a false base case, a
//! non-inductive step, and a wrong post-loop value are all refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_itlc_{}_{}.rs", std::process::id(), tmp_id));
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
// upstream basic_loop (Ok): the native form of the ghost `int` counter.
#[trust_vc::ensures(true)]
pub fn basic_loop_int_counter() {
    let mut a: int = 5int;
    loop {
        trust_vc::invariant!(a > 0int);
        a = a + 1int;
    }
}

// LIAR: the invariant is not preserved.
#[trust_vc::ensures(true)]
pub fn int_counter_non_inductive_invariant() {
    let mut a: int = 5int;
    loop {
        trust_vc::invariant!(a == 5int);
        a = a + 1int;
    }
}

// LIAR: the invariant is false at entry.
#[trust_vc::ensures(true)]
pub fn int_counter_false_base_case() {
    let mut a: int = 5int;
    loop {
        trust_vc::invariant!(a == 0int);
        a = a;
    }
}

// A `nat` counter: the floor and the invariant both hold.
#[trust_vc::ensures(true)]
pub fn nat_counter_loop() {
    let mut n: nat = 0nat;
    loop {
        trust_vc::invariant!(n >= 0nat);
        n = n + 1nat;
    }
}

// An `int` counter through a break site and out to a post-loop fact (the
// upstream example_loop_break shape: except-break bound, regular floor, ensures).
#[trust_vc::ensures(true)]
pub fn int_counter_break_site_post_loop_fact() {
    let mut a: int = 0int;
    loop {
        trust_vc::invariant_except_break!(a <= 9int);
        trust_vc::invariant!(a >= 0int);
        trust_vc::loop_ensures!(a == 10int);
        a = a + 1int;
        if a == 10int {
            break;
        }
    }
    trust_vc::assert!(a == 10int);
}

// LIAR: the post-loop value is not 11.
#[trust_vc::ensures(true)]
pub fn int_counter_break_site_wrong_post_loop_value() {
    let mut a: int = 0int;
    loop {
        trust_vc::invariant_except_break!(a <= 9int);
        trust_vc::invariant!(a >= 0int);
        trust_vc::loop_ensures!(a == 10int);
        a = a + 1int;
        if a == 10int {
            break;
        }
    }
    trust_vc::assert!(a == 11int);
}

// A `while` over an `int` counter keeps its normal-exit fact.
#[trust_vc::ensures(true)]
pub fn int_counter_while_normal_exit() {
    let mut i: int = 0int;
    while i < 10int {
        trust_vc::invariant!(i <= 10int);
        i = i + 1int;
    }
    trust_vc::assert!(i == 10int);
}

// LIAR: the exit value is not 9.
#[trust_vc::ensures(true)]
pub fn int_counter_while_wrong_exit_value() {
    let mut i: int = 0int;
    while i < 10int {
        trust_vc::invariant!(i <= 10int);
        i = i + 1int;
    }
    trust_vc::assert!(i == 9int);
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
fn upstream_basic_loop_int_counter_verifies() {
    expect_verified("c1", "basic_loop_int_counter");
}

#[test]
fn liar_int_counter_non_inductive_invariant_is_rejected() {
    expect_counterexample("l1", "int_counter_non_inductive_invariant");
}

#[test]
fn liar_int_counter_false_base_case_is_rejected() {
    expect_counterexample("l2", "int_counter_false_base_case");
}

#[test]
fn nat_counter_loop_verifies() {
    expect_verified("c2", "nat_counter_loop");
}

#[test]
fn int_counter_break_site_post_loop_fact_verifies() {
    expect_verified("c3", "int_counter_break_site_post_loop_fact");
}

#[test]
fn liar_int_counter_break_site_wrong_post_loop_value_is_rejected() {
    expect_counterexample("l3", "int_counter_break_site_wrong_post_loop_value");
}

#[test]
fn int_counter_while_normal_exit_verifies() {
    expect_verified("c4", "int_counter_while_normal_exit");
}

#[test]
fn liar_int_counter_while_wrong_exit_value_is_rejected() {
    expect_counterexample("l4", "int_counter_while_wrong_exit_value");
}
