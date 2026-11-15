// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 430/431 — nested loops that MODIFY state inside
//! an exact outer body, 2026-09-10): a nested `while` with a side-effect-free
//! guard (or a bare `loop {}`) whose body is flat, that cannot `break`, and
//! that cannot leave the enclosing loop is SUMMARIZED for the enclosing
//! transition: every var it modifies ↦ a fresh exit symbol, plus its exit facts
//! (invariants, `loop_ensures`, negated guard) in the head-to-head guard and in
//! the guards of the exit / continue sites AFTER it. Upstream loop_decreases2
//! (nested counters with measures) is the headline shape. The liars pin the
//! scope of the facts: not at a site before the nested loop, not as a
//! post-loop fact of the enclosing loop, and only what the nested loop's own
//! spec states.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nmls_{}_{}.rs", std::process::id(), tmp_id));
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
// upstream loop_decreases2::test1 (Ok): nested counters, both with measures.
#[trust_vc::ensures(true)]
pub fn loop_decreases2_test1() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);
        while j > 0 {
            trust_vc::loop_decreases!(j);
            j = j - 1;
        }
        i = i - 1;
    }
    trust_vc::assert!(i == 0);
}

// upstream loop_decreases2::test2 (FAILS): the inner measure never decreases.
#[trust_vc::ensures(true)]
pub fn loop_decreases2_test2() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);
        while j > 0 {
            trust_vc::loop_decreases!(j);
        }
        i = i - 1;
    }
}

// upstream loop_decreases2::test3 (FAILS): the outer measure never decreases.
#[trust_vc::ensures(true)]
pub fn loop_decreases2_test3() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);
        while j > 0 {
            trust_vc::loop_decreases!(j);
            j = j - 1;
        }
    }
}

// CONTROL: the outer invariant over `j` is preserved only through the inner
// loop's exit facts (`j <= 5` from its invariant).
#[trust_vc::ensures(true)]
pub fn outer_invariant_preserved_by_inner_exit_facts(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 5u64);
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(j <= 5u64);
}

// LIAR: the exit facts are exactly the inner spec — `j == 5` after the inner
// loop refutes an outer invariant `j <= 4`.
#[trust_vc::ensures(true)]
pub fn outer_invariant_refuted_by_inner_exit_facts(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 4u64);
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
        }
        i = i + 1u64;
    }
}

// CONTROL: a body assertion AFTER the inner loop sees its exit facts.
#[trust_vc::ensures(true)]
pub fn body_assertion_after_inner_loop_sees_exit_facts(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 5u64);
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
        }
        trust_vc::assert!(j == 5u64);
        i = i + 1u64;
    }
}

// LIAR: … and not the stale loop-head value of `j`.
#[trust_vc::ensures(true)]
pub fn body_assertion_after_inner_loop_not_stale(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(j <= 5u64);
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
        }
        trust_vc::assert!(j == 0u64);
        i = i + 1u64;
    }
}

// LIAR: an exit site BEFORE the inner loop does not see its facts.
#[trust_vc::ensures(true)]
pub fn exit_site_before_inner_loop_has_no_inner_facts(b: bool) {
    let mut j: u64 = 0;
    loop {
        trust_vc::invariant!(j <= 5u64);
        trust_vc::loop_ensures!(j == 5u64);
        if b {
            break;
        }
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
        }
    }
}

// LIAR: an inner loop that never exits makes the rest of the BODY unreachable,
// not the code after the enclosing loop (which exits through `break`).
#[trust_vc::ensures(true)]
pub fn inner_infinite_loop_does_not_reach_past_outer_loop(b: bool) {
    let mut j: u64 = 0;
    loop {
        trust_vc::invariant!(true);
        if b {
            break;
        }
        loop {
            trust_vc::invariant!(true);
            j = 1u64;
        }
    }
    trust_vc::assert!(false);
}

// LIAR (nested entry): the inner invariant `total <= 5` holds at the FIRST
// outer iteration (total enters at 1) but not later (total grows outside the
// inner loop); the inner base case must not prove it from `requires(total == 0)`.
#[trust_vc::requires(total == 0u64)]
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn inner_base_case_must_not_use_function_entry_facts(mut total: u64, n: u64) {
    let mut i: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total <= 6u64 * i);
        total = total + 1u64;
        while total < 3u64 {
            trust_vc::invariant!(total <= 5u64);
            total = total + 1u64;
        }
        i = i + 1u64;
    }
}

// CONTROL (nested entry): the same shape with an inner invariant the enclosing
// head facts DO support.
#[trust_vc::requires(total == 0u64)]
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
pub fn inner_base_case_from_enclosing_head_facts(mut total: u64, n: u64) {
    let mut i: u64 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(total <= 6u64 * i);
        total = total + 1u64;
        while total < 3u64 {
            trust_vc::invariant!(total <= 6u64 * i + 3u64);
            total = total + 1u64;
        }
        i = i + 1u64;
    }
}

// LIAR: the outer invariant on `i` still needs the outer transition.
#[trust_vc::ensures(true)]
pub fn outer_invariant_not_preserved_is_refuted(n: u64) {
    let mut i: u64 = 0;
    let mut j: u64 = 0;
    while i < n {
        trust_vc::invariant!(i == 0u64);
        while j < 5u64 {
            trust_vc::invariant!(j <= 5u64);
            j = j + 1u64;
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
fn upstream_loop_decreases2_test1_verifies() {
    expect_verified("c1", "loop_decreases2_test1");
}

#[test]
fn upstream_loop_decreases2_test2_is_rejected() {
    expect_counterexample("l1", "loop_decreases2_test2");
}

#[test]
fn upstream_loop_decreases2_test3_is_rejected() {
    expect_counterexample("l2", "loop_decreases2_test3");
}

#[test]
fn control_outer_invariant_preserved_by_inner_exit_facts() {
    expect_verified("c2", "outer_invariant_preserved_by_inner_exit_facts");
}

#[test]
fn liar_outer_invariant_refuted_by_inner_exit_facts() {
    expect_counterexample("l3", "outer_invariant_refuted_by_inner_exit_facts");
}

#[test]
fn control_body_assertion_after_inner_loop_sees_exit_facts() {
    expect_verified("c3", "body_assertion_after_inner_loop_sees_exit_facts");
}

#[test]
fn liar_body_assertion_after_inner_loop_not_stale() {
    expect_counterexample("l4", "body_assertion_after_inner_loop_not_stale");
}

#[test]
fn liar_exit_site_before_inner_loop_has_no_inner_facts() {
    expect_counterexample("l5", "exit_site_before_inner_loop_has_no_inner_facts");
}

#[test]
fn liar_inner_infinite_loop_does_not_reach_past_outer_loop() {
    expect_counterexample("l6", "inner_infinite_loop_does_not_reach_past_outer_loop");
}

#[test]
fn liar_inner_base_case_must_not_use_function_entry_facts() {
    expect_counterexample("l8", "inner_base_case_must_not_use_function_entry_facts");
}

#[test]
fn control_inner_base_case_from_enclosing_head_facts() {
    expect_verified("c4", "inner_base_case_from_enclosing_head_facts");
}

#[test]
fn liar_outer_invariant_not_preserved_is_refuted() {
    expect_counterexample("l7", "outer_invariant_not_preserved_is_refuted");
}
