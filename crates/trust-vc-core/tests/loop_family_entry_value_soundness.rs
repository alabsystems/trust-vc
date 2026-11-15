// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS GUARD — the loop ENTRY-VALUE class across every guard-less loop
//! form on the file path: bare `loop {}` (see
//! `bare_loop_invariant_capability.rs`), `for` over a range whose body is too
//! rich for the range desugar, and `while let`.
//!
//! Measured before the fix (2026-09-10): with an `invariant!` present, none of
//! these forms pushed a loop-extraction context, so no `loop_modified_vars`
//! were registered for the invariant. The post-loop frame only INVALIDATED the
//! modified vars and relied on the encoder's havoc — which never came — so a
//! loop-modified param fell back to its `requires` ENTRY symbol after the loop,
//! and the body's exec arithmetic was checked at the entry value instead of an
//! arbitrary loop head. Three liars below were `Verified`:
//!
//!   * `for_stale_entry_liar`        — Verified (now Counterexample)
//!   * `while_let_stale_entry_liar`  — Verified (now Counterexample)
//!   * `while_let_body_overflow_liar` — Verified (now Counterexample)
//!
//! `for_body_overflow_liar` already failed closed (the loop binding in the path
//! condition is unresolved) and the no-invariant `for` already havocked — both
//! stay pinned so the fix is not allowed to widen into over-acceptance either.
//! The positive controls keep the fix from over-rejecting: an invariant over
//! UNMODIFIED state still verifies and still reaches the post-loop assertion.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lfe_{}_{}.rs", std::process::id(), tmp_id));
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

const FOR_LOOPS: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn for_stale_entry_liar(mut i: u64) {
    for k in 0u64..3u64 {
        trust_vc::invariant!(true);
        if k == 1u64 {
            i = 5u64;
        }
    }
    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(x == 18446744073709551465u64)]
#[trust_vc::ensures(true)]
pub fn for_body_overflow_liar(mut x: u64) {
    for k in 0u64..3u64 {
        trust_vc::invariant!(true);
        if k < 3u64 {
            x = x + 100u64;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn for_no_invariant_stale_entry_liar(mut i: u64) {
    for k in 0u64..3u64 {
        if k == 1u64 {
            i = 5u64;
        }
    }
    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn for_unmodified_invariant_true(mut i: u64, limit: u64) {
    for k in 0u64..3u64 {
        trust_vc::invariant!(limit == 10u64);
        if k == 1u64 {
            i = 5u64;
        }
    }
    trust_vc::assert!(limit == 10u64);
}
"#;

const WHILE_LET: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn while_let_stale_entry_liar(mut i: u64, mut o: Option<u64>) {
    while let Some(_v) = o {
        trust_vc::invariant!(true);
        i = 5u64;
        o = None;
    }
    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(x == 18446744073709551465u64)]
#[trust_vc::ensures(true)]
pub fn while_let_body_overflow_liar(mut x: u64, mut o: Option<u64>) {
    while let Some(_v) = o {
        trust_vc::invariant!(true);
        x = x + 100u64;
        o = None;
    }
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn while_let_unmodified_invariant_true(mut i: u64, mut o: Option<u64>, limit: u64) {
    while let Some(_v) = o {
        trust_vc::invariant!(limit == 10u64);
        i = 5u64;
        o = None;
    }
    trust_vc::assert!(limit == 10u64);
}
"#;

fn assert_not_verified(label: &str, result: VerifyResult) {
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{label}: a LIAR must never verify: {result:?}"
    );
}

fn assert_counterexample(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label}: must be refuted with a counterexample: {result:?}"
    );
}

#[test]
fn for_loop_stale_entry_read_is_refuted() {
    assert_counterexample(
        "for_stale_entry_liar",
        verify("f1", "for_stale_entry_liar", FOR_LOOPS),
    );
}

#[test]
fn for_loop_body_overflow_does_not_verify() {
    assert_not_verified(
        "for_body_overflow_liar",
        verify("f2", "for_body_overflow_liar", FOR_LOOPS),
    );
}

#[test]
fn for_loop_no_invariant_stale_entry_read_is_refuted() {
    assert_counterexample(
        "for_no_invariant_stale_entry_liar",
        verify("f3", "for_no_invariant_stale_entry_liar", FOR_LOOPS),
    );
}

#[test]
fn for_loop_unmodified_state_invariant_still_verifies() {
    let result = verify("f4", "for_unmodified_invariant_true", FOR_LOOPS);
    assert!(
        matches!(result, VerifyResult::Verified),
        "no over-rejection: an unmodified-state invariant on a non-flat `for` must verify \
         and reach the post-loop assertion: {result:?}"
    );
}

#[test]
fn while_let_stale_entry_read_is_refuted() {
    assert_counterexample(
        "while_let_stale_entry_liar",
        verify("w1", "while_let_stale_entry_liar", WHILE_LET),
    );
}

#[test]
fn while_let_body_overflow_is_refuted() {
    assert_counterexample(
        "while_let_body_overflow_liar",
        verify("w2", "while_let_body_overflow_liar", WHILE_LET),
    );
}

#[test]
fn while_let_unmodified_state_invariant_still_verifies() {
    let result = verify("w3", "while_let_unmodified_invariant_true", WHILE_LET);
    assert!(
        matches!(result, VerifyResult::Verified),
        "no over-rejection: an unmodified-state invariant on a `while let` must verify \
         and reach the post-loop assertion: {result:?}"
    );
}
