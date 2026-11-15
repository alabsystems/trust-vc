// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 430 residual — assertions inside a loop body see
//! the loop-head facts): an `assert!` in a loop body is checked at an
//! arbitrary loop head under the guard and EVERY invariant, `invariant_except_
//! break` included, with the body's earlier assignments substituted — the
//! Verus rule. Before, the bare rendering reached only the regular verified
//! invariants (no guard, no except-break facts), which kept upstream
//! `example_loop_break`'s in-body `assert(i <= 9)` out of the port.
//!
//! Every positive has a liar one bound tighter; the entry value must never be
//! what discharges a body assertion.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lbh_{}_{}.rs", std::process::id(), tmp_id));
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
// Upstream example_loop_break, in-body assertion included.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn except_break_fact_reaches_body_assert(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn except_break_fact_body_assert_liar(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::assert!(i <= 8u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

// The while guard is a head fact for the body.
#[trust_vc::ensures(true)]
pub fn guard_reaches_body_assert(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(true);
        trust_vc::assert!(i < n);
        i = i + 1u64;
    }
}

#[trust_vc::ensures(true)]
pub fn guard_body_assert_liar(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(true);
        trust_vc::assert!(i + 1u64 < n);
        i = i + 1u64;
    }
}

// An assertion AFTER a body assignment reads the updated value.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
pub fn assert_after_assignment(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        trust_vc::assert!(i <= 10u64);
    }
}

#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
pub fn assert_after_assignment_liar(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        trust_vc::assert!(i <= 9u64);
    }
}

// SOUNDNESS: the entry value of a modified var never discharges a body assert.
// (A bare loop: a `while` with `requires(i == 0)` trips the whole-function
// vacuity precheck against its own negated-guard exit fact — a pre-existing
// over-rejection, recorded in the ledger, that would mask this probe.)
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn entry_value_does_not_discharge_body_assert(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::assert!(i == 0u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
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
fn except_break_invariant_is_a_head_fact_for_body_assertions() {
    expect_verified(
        "except_break_fact_reaches_body_assert",
        verify("a1", "except_break_fact_reaches_body_assert", SRC),
    );
}

#[test]
fn except_break_invariant_does_not_prove_a_tighter_body_assertion() {
    expect_counterexample(
        "except_break_fact_body_assert_liar",
        verify("a2", "except_break_fact_body_assert_liar", SRC),
    );
}

#[test]
fn while_guard_is_a_head_fact_for_body_assertions() {
    expect_verified(
        "guard_reaches_body_assert",
        verify("a3", "guard_reaches_body_assert", SRC),
    );
}

#[test]
fn while_guard_does_not_prove_a_tighter_body_assertion() {
    expect_counterexample(
        "guard_body_assert_liar",
        verify("a4", "guard_body_assert_liar", SRC),
    );
}

#[test]
fn body_assertion_after_an_assignment_reads_the_updated_value() {
    expect_verified(
        "assert_after_assignment",
        verify("a5", "assert_after_assignment", SRC),
    );
}

#[test]
fn body_assertion_after_an_assignment_refutes_a_tighter_bound() {
    expect_counterexample(
        "assert_after_assignment_liar",
        verify("a6", "assert_after_assignment_liar", SRC),
    );
}

#[test]
fn entry_value_never_discharges_a_body_assertion_soundness() {
    expect_counterexample(
        "entry_value_does_not_discharge_body_assert",
        verify("a7", "entry_value_does_not_discharge_body_assert", SRC),
    );
}
