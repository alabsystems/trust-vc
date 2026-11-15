// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 430 — unconditional trailing `break;` / `continue;`):
//! as the LAST statement of an otherwise flat body, `break;` is an exit site
//! reached unconditionally (exit checks run there; the head-to-head step is
//! vacuous because no iteration follows) and `continue;` is a no-op. Anywhere
//! else they keep the body in the havoc lane. This is upstream
//! `loop_continue_no_break` (one verified, three failing functions),
//! `loop_break_false`, and the immediate-break `example_loop_break_fail3`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lte_{}_{}.rs", std::process::id(), tmp_id));
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
// upstream loop_continue_no_break::test_loop (Ok), made terminating: upstream's
// body is a bare `continue;` over an unmodified counter, so the loop never
// exits once entered and its post-loop assertion is vacuous — Verus passes it
// as unreachable, trust-vc reports the vacuity as Unknown by design. With the
// increment the trailing continue is a genuine no-op and the loop verifies.
#[trust_vc::ensures(true)]
pub fn continue_no_break_test_loop() {
    let mut i = 0u64;
    while i < 5u64 {
        trust_vc::invariant!(i <= 5u64);
        i = i + 1u64;
        continue;
    }
    trust_vc::assert!(i == 5u64);
}

// upstream test_fail_beginning (FAILS): the invariant is false at entry.
#[trust_vc::ensures(true)]
pub fn continue_no_break_fail_beginning() {
    let mut x = 0u64;
    let mut i = 7u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 1u64);
        x = 1u64;
        continue;
    }
}

// upstream test_fail_at_continue (FAILS): `x = 1` then continue breaks `x == 2`.
// Upstream's `let mut i = 7` never runs the loop (Verus's isolated body check
// fails anyway; trust-vc value-numbers the unmodified local and the step is
// vacuous — the code is correct), and an unmodified counter under a
// `requires(i < 5)` never exits (whole-function vacuity, reported as Unknown).
// The counter is incremented here so the loop is reachable AND terminating,
// and the broken invariant is what refutes.
#[trust_vc::requires(i < 5u64)]
#[trust_vc::ensures(true)]
pub fn continue_no_break_fail_at_continue(mut i: u64) {
    let mut x = 2u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 2u64);
        x = 1u64;
        i = i + 1u64;
        continue;
    }
}

// upstream test_fail_at_end_after_continue (FAILS): the fall-through sets x = 1
// (same reachable-counter adjustment as above).
#[trust_vc::requires(i < 5u64)]
#[trust_vc::ensures(true)]
pub fn continue_no_break_fail_at_end_after_continue(b: bool, mut i: u64) {
    let mut x = 2u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 2u64);
        i = i + 1u64;
        if b {
            continue;
        }
        x = 1u64;
    }
}

// upstream loop_break_false (FAILS): the break reaches the assertion.
#[trust_vc::ensures(true)]
pub fn loop_break_false() {
    loop {
        break;
    }
    trust_vc::assert!(false);
}

// upstream example_loop_break_fail3 (FAILS): the immediate break exits with
// i == 0 and the loop ensures `1 <= i` is checked AT that exit.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_fail3(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        break;
    }
    trust_vc::assert!(1u64 <= i);
}

// A trailing break carries its loop ensures past the loop.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn trailing_break_carries_ensures(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(i == 5u64);
        i = 5u64;
        break;
    }
    trust_vc::assert!(i == 5u64);
}

// ... and only what it checked: without the ensures, `i == 5` is not a post-loop fact.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn trailing_break_without_ensures_liar(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        i = 5u64;
        break;
    }
    trust_vc::assert!(i == 5u64);
}
"#;

fn expect_verified(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label} must verify: {result:?}"
    );
}

fn expect_counterexample(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label} must be refuted with a counterexample: {result:?}"
    );
}

#[test]
fn trailing_continue_is_a_no_op_and_the_loop_verifies() {
    expect_verified(
        "continue_no_break_test_loop",
        verify("t1", "continue_no_break_test_loop", SRC),
    );
}

#[test]
fn invariant_false_at_entry_refutes() {
    expect_counterexample(
        "continue_no_break_fail_beginning",
        verify("t2", "continue_no_break_fail_beginning", SRC),
    );
}

#[test]
fn invariant_broken_before_a_trailing_continue_refutes() {
    expect_counterexample(
        "continue_no_break_fail_at_continue",
        verify("t3", "continue_no_break_fail_at_continue", SRC),
    );
}

#[test]
fn invariant_broken_on_the_fall_through_after_a_continue_site_refutes() {
    expect_counterexample(
        "continue_no_break_fail_at_end_after_continue",
        verify("t4", "continue_no_break_fail_at_end_after_continue", SRC),
    );
}

#[test]
fn trailing_break_still_reaches_the_following_assertion() {
    expect_counterexample("loop_break_false", verify("t5", "loop_break_false", SRC));
}

#[test]
fn immediate_break_refutes_the_loop_ensures_at_the_exit() {
    expect_counterexample(
        "example_loop_break_fail3",
        verify("t6", "example_loop_break_fail3", SRC),
    );
}

#[test]
fn trailing_break_carries_its_loop_ensures_past_the_loop() {
    expect_verified(
        "trailing_break_carries_ensures",
        verify("t7", "trailing_break_carries_ensures", SRC),
    );
}

#[test]
fn trailing_break_carries_only_the_checked_predicates() {
    expect_counterexample(
        "trailing_break_without_ensures_liar",
        verify("t8", "trailing_break_without_ensures_liar", SRC),
    );
}
