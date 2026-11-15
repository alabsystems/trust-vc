// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (mut_refs_loops `control_flow_loops*` /
//! `future_preserved_in_loop`, 2026-09-13): ONE plain write through a
//! pre-borrowed `&mut` alias — or a direct scalar `&mut` parameter — inside a
//! loop body keeps exact per-iteration modeling. The alias's ROOT joins the
//! loop's modified set (bare inside the body, havocked or invariant-framed
//! after the loop), the alias mapping survives the body-entry invalidation
//! valued at that framed root, and the first in-body write resolves it. The
//! liars pin what stays closed: a second write in the same body and a
//! compound write are still gated, a read before the write sees the framed
//! root (never the pre-loop value), and post-loop reads never see a stale or
//! an assumed written value.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_mrdl_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL (pre-borrowed alias, bare loop): the corpus shape with a TRUE read-back.
#[trust_vc::ensures(true)]
fn preborrow_write_readback_verifies() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    loop {
        *value_ref = 5u64;
        trust_vc::assert!(value == 5u64);
        trust_vc::assert!(*value_ref == 5u64);
        return;
    }
}

// LIAR (the corpus counterexample): the wrong written value is refuted.
#[trust_vc::ensures(true)]
fn preborrow_wrong_writeback_liar() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    loop {
        *value_ref = 5u64;
        trust_vc::assert!(value == 6u64);
        return;
    }
}

// CONTROL (alias declared inside the OUTER loop body, written in the inner loop).
#[trust_vc::ensures(true)]
fn nested_local_alias_write_verifies(run: bool) {
    'outer: loop {
        if !run {
            break;
        }
        loop {
            let mut x = 0u64;
            let x_ref: &mut u64 = &mut x;
            loop {
                *x_ref = 20u64;
                trust_vc::assert!(x == 20u64);
                trust_vc::assert!(*x_ref == 20u64);
                break 'outer;
            }
        }
    }
}

// CONTROL (direct `&mut` param, `while`): single write + assert stays exact.
#[trust_vc::requires(x == 5u64)]
fn param_write_in_while_verifies(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 20u64;
        trust_vc::assert!(*x == 20u64);
        i += 1u64;
    }
}

// LIAR: … and the wrong value is refuted.
#[trust_vc::requires(x == 5u64)]
fn param_write_in_while_liar(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 20u64;
        trust_vc::assert!(*x == 21u64);
        i += 1u64;
    }
}

// LIAR (SOUNDNESS): a read BEFORE the write must not see the pre-loop value —
// on the second iteration the root is already 5.
#[trust_vc::ensures(true)]
fn read_before_write_sees_framed_root_liar(n: u64) {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(value == 0u64);
        *value_ref = 5u64;
        i += 1u64;
    }
}

// LIAR (SOUNDNESS): the post-loop read never sees the stale pre-loop value …
#[trust_vc::ensures(true)]
fn post_loop_stale_read_liar(n: u64) {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let mut i = 0u64;
    while i < n {
        *value_ref = 5u64;
        i += 1u64;
    }
    trust_vc::assert!(value == 0u64);
}

// … and the written value is not assumed either (the loop may run zero times).
#[trust_vc::ensures(true)]
fn post_loop_written_read_liar(n: u64) {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;
    let mut i = 0u64;
    while i < n {
        *value_ref = 5u64;
        i += 1u64;
    }
    trust_vc::assert!(value == 5u64);
}

// GATED: a SECOND deref write in the same body keeps the verbatim refusal.
#[trust_vc::requires(x == 0u64)]
fn second_write_in_body_gated(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 1u64;
        *x = 2u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 0u64);
}

// GATED: a compound deref write keeps the verbatim refusal.
#[trust_vc::requires(x == 0u64)]
fn compound_write_in_body_gated(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x += 1u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 0u64);
}
"#;

const DEREF_REFUSAL: &str = "assignment through a dereferenced reference is unsupported";

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

fn expect_never_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

fn expect_gated(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Error { message } if message.contains(DEREF_REFUSAL) => {}
        other => panic!("{func}: expected the verbatim deref-write refusal, got {other:?}"),
    }
}

#[test]
fn control_preborrow_write_readback_verifies() {
    expect_verified("c1", "preborrow_write_readback_verifies");
}

#[test]
fn liar_preborrow_wrong_writeback_is_refuted() {
    expect_counterexample("l1", "preborrow_wrong_writeback_liar");
}

#[test]
fn control_nested_local_alias_write_verifies() {
    expect_verified("c2", "nested_local_alias_write_verifies");
}

#[test]
fn control_param_write_in_while_verifies() {
    expect_verified("c3", "param_write_in_while_verifies");
}

#[test]
fn liar_param_write_in_while_is_refuted() {
    expect_counterexample("l2", "param_write_in_while_liar");
}

#[test]
fn liar_read_before_write_does_not_see_the_pre_loop_value() {
    expect_never_verified("l3", "read_before_write_sees_framed_root_liar");
}

#[test]
fn liar_post_loop_stale_read_is_never_verified() {
    expect_never_verified("l4", "post_loop_stale_read_liar");
}

#[test]
fn liar_post_loop_written_read_is_never_verified() {
    expect_never_verified("l5", "post_loop_written_read_liar");
}

#[test]
fn second_write_in_body_stays_gated() {
    expect_gated("g1", "second_write_in_body_gated");
}

#[test]
fn compound_write_in_body_stays_gated() {
    expect_gated("g2", "compound_write_in_body_gated");
}
