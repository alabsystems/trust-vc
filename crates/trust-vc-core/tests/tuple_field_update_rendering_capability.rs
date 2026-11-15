// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (mut_refs_loops `future_preserved_in_loop` tuple-field
//! write-back, 2026-09-13): a field write on a TUPLE-typed place — an owned
//! tuple local `p.0 = v`, a `&mut (A, B)` parameter `pair_ref.1 = v`, or the
//! same after a loop — renders as a tuple literal with that component
//! replaced. Before, the struct-update spelling (`(u64, u64) { 0: v, ..recv }`)
//! was emitted for tuple types too and failed to PARSE at lowering, so every
//! such write failed closed. The liars pin that the untouched components keep
//! their values and that a wrong claim is refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tfur_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL: an owned tuple local.
#[trust_vc::ensures(true)]
fn owned_tuple_field_write_verifies() {
    let mut p = (1u64, 2u64);
    p.0 = 5u64;
    trust_vc::assert!(p.0 == 5u64);
    trust_vc::assert!(p.1 == 2u64);
}

// LIAR: the other component is not written.
#[trust_vc::ensures(true)]
fn owned_tuple_field_write_liar() {
    let mut p = (1u64, 2u64);
    p.0 = 5u64;
    trust_vc::assert!(p.1 == 5u64);
}

// LIAR (SOUNDNESS): the write was DROPPED before — a stale claim must not verify.
#[trust_vc::ensures(true)]
fn owned_tuple_stale_read_liar() {
    let mut p = (1u64, 2u64);
    p.0 = 5u64;
    trust_vc::assert!(p.0 == 1u64);
}

// CONTROL: a `&mut (u64, u64)` parameter, both components written in turn.
#[trust_vc::ensures(true)]
fn param_tuple_field_writes_verify(pair_ref: &mut (u64, u64)) {
    pair_ref.0 = 5u64;
    pair_ref.1 = 6u64;
    trust_vc::assert!(pair_ref.0 == 5u64);
    trust_vc::assert!(pair_ref.1 == 6u64);
}

// LIAR: … and the second write does not touch the first component.
#[trust_vc::ensures(true)]
fn param_tuple_field_writes_liar(pair_ref: &mut (u64, u64)) {
    pair_ref.0 = 5u64;
    pair_ref.1 = 6u64;
    trust_vc::assert!(pair_ref.0 == 6u64);
}

// CONTROL (the corpus shape): a loop write, then post-loop writes and reads.
#[trust_vc::ensures(true)]
fn loop_then_tuple_field_writeback_verifies(pair_ref: &mut (u64, u64)) {
    loop {
        pair_ref.0 = 20u64;
        break;
    }
    pair_ref.0 = 5u64;
    pair_ref.1 = 6u64;
    trust_vc::assert!(pair_ref.0 == 5u64);
    trust_vc::assert!(pair_ref.1 == 6u64);
}

// CONTROL: a 3-tuple, the middle component.
#[trust_vc::ensures(true)]
fn three_tuple_middle_write_verifies() {
    let mut t = (1u64, 2u64, 3u64);
    t.1 = 20u64;
    trust_vc::assert!(t.0 == 1u64);
    trust_vc::assert!(t.1 == 20u64);
    trust_vc::assert!(t.2 == 3u64);
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
fn control_owned_tuple_field_write_verifies() {
    expect_verified("c1", "owned_tuple_field_write_verifies");
}

#[test]
fn liar_owned_tuple_field_write_is_refuted() {
    expect_counterexample("l1", "owned_tuple_field_write_liar");
}

#[test]
fn liar_owned_tuple_stale_read_is_refuted() {
    expect_counterexample("l0", "owned_tuple_stale_read_liar");
}

#[test]
fn control_param_tuple_field_writes_verify() {
    expect_verified("c2", "param_tuple_field_writes_verify");
}

#[test]
fn liar_param_tuple_field_writes_are_refuted() {
    expect_counterexample("l2", "param_tuple_field_writes_liar");
}

#[test]
fn control_loop_then_tuple_field_writeback_verifies() {
    expect_verified("c3", "loop_then_tuple_field_writeback_verifies");
}

#[test]
fn control_three_tuple_middle_write_verifies() {
    expect_verified("c4", "three_tuple_middle_write_verifies");
}
