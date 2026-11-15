// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (`old()` as a two-state READ, 2026-09-13).
//!
//! The body-side visitors routed `old(P)` through the unknown-callee
//! `&mut`-argument fallback, so the operator HAVOCED / invalidated `P`: a
//! later `*P` read fell back to the bare entry symbol (`*x = 10;
//! assert!(old(x) == 5); assert!(*x == 10)` counterexampled), a later
//! `*P = ..` was refused as an untracked deref write, and the escape
//! detector counted the bare `P` inside `old(P)` as a reference escape. The
//! operator is now a pure read of the entry state everywhere: no havoc, no
//! escape, no loop write.
//!
//! The same measurement found THREE live false `Verified`s where the bare
//! entry symbol `P` no longer meant the entry value: inside a loop body that
//! modifies `P` (the inductive step havocs it — `assert!(*old(x) == *x)`
//! before the write rendered `x == x`), after a completed loop WITH
//! invariants that modified `P` (its post-loop state IS the bare symbol, with
//! the exit fact assumed over it — `while *x != 7 { invariant!(true); *x =
//! 7; } assert!(*old(x) == 7)` verified for an arbitrary entry), and the same
//! shape in `ensures`. Those are now refused with a precise error until the
//! entry value of a loop-modified `&mut` param gets its own symbol. A loop
//! WITHOUT invariants rebinds `P` to a fresh havoc symbol and leaves the
//! entry symbol intact, so `old(P)` after it stays exact (pinned below).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_mrots_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL: a write, an old() assertion, then a CURRENT read.
#[trust_vc::requires(x == 5u64)]
fn write_then_old_then_read_verifies(x: &mut u64) {
    *x = 10u64;
    trust_vc::assert!(old(x) == 5u64);
    trust_vc::assert!(*x == 10u64);
}

// LIAR: the current read after old() is the WRITTEN value, not the entry.
#[trust_vc::requires(x == 5u64)]
fn current_read_after_old_liar(x: &mut u64) {
    *x = 10u64;
    trust_vc::assert!(old(x) == 5u64);
    trust_vc::assert!(*x == 5u64);
}

// LIAR (the time-travel direction): old() never reads the post state.
#[trust_vc::requires(x == 5u64)]
fn old_reads_entry_not_current_liar(x: &mut u64) {
    *x = 10u64;
    trust_vc::assert!(*old(x) == 10u64);
}

// CONTROL: an old() assertion BEFORE the write no longer disables the write.
#[trust_vc::requires(x == 5u64)]
fn old_before_write_then_read_verifies(x: &mut u64) {
    trust_vc::assert!(old(x) == 5u64);
    *x = 10u64;
    trust_vc::assert!(*x == 10u64);
}

// CONTROL: old() in a let initializer, then a write.
#[trust_vc::requires(x == 5u64)]
fn old_in_let_then_write_verifies(x: &mut u64) {
    let e = *old(x);
    *x = 10u64;
    trust_vc::assert!(*x == 10u64);
    trust_vc::assert!(e == 5u64);
}

// CONTROL (upstream basic.rs:613 shape): old() on the RHS of the write.
#[trust_vc::requires(*old(y) < 100u64)]
fn old_rhs_write_verifies(y: &mut u64) {
    *y = *old(y) / 2u64;
    trust_vc::assert!(*y == *old(y) / 2u64);
}

// LIAR: … and the wrong relation is refuted.
#[trust_vc::requires(*old(y) < 100u64)]
#[trust_vc::requires(*old(y) >= 10u64)]
fn old_rhs_wrong_relation_liar(y: &mut u64) {
    *y = *old(y) / 2u64;
    trust_vc::assert!(*y == *old(y));
}

// CONTROL: a write through a param-derived alias, then old() and both reads.
#[trust_vc::requires(x == 5u64)]
fn alias_write_old_then_read_verifies(x: &mut u64) {
    let r: &mut u64 = x;
    *r = 10u64;
    trust_vc::assert!(*old(x) == 5u64);
    trust_vc::assert!(*r == 10u64);
    trust_vc::assert!(*x == 10u64);
}

// CONTROL: a body old() does not count as an escape for the ensures resolver.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(*x == 7u64 && *old(x) == 0u64)]
fn old_then_write_ensures_final_verifies(x: &mut u64) {
    trust_vc::assert!(*old(x) == 0u64);
    *x = 7u64;
}

// CONTROL: old() across a compound chain (the mut_ref_compound_assign shape).
#[trust_vc::requires(x == 5u64)]
fn compound_chain_then_old_verifies(x: &mut u64) {
    *x = 10u64;
    *x += 4u64;
    trust_vc::assert!(old(x) == 5u64);
    trust_vc::assert!(*x == 14u64);
}

// CONTROL: old() inside a loop body that does NOT modify the param.
#[trust_vc::requires(x == 0u64)]
fn old_in_unmodifying_loop_body_verifies(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(*old(x) == 0u64);
        i += 1u64;
    }
}

// CONTROL: old() AFTER a loop without invariants that wrote the param — the
// loop havocs the param to a fresh symbol, the entry symbol stays exact.
#[trust_vc::requires(x == 0u64)]
fn old_after_no_invariant_loop_verifies(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 7u64;
        i += 1u64;
    }
    trust_vc::assert!(*old(x) == 0u64);
}

// LIAR (was a false Verified: `x == x`): after that loop the current value is
// NOT the entry value.
#[trust_vc::requires(x == 0u64)]
fn old_after_no_invariant_loop_liar(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 7u64;
        i += 1u64;
    }
    trust_vc::assert!(*old(x) == *x);
}

// GATED (was a false Verified: `x == x` with `x` the loop-head symbol):
// old() inside a loop body that modifies the param.
#[trust_vc::requires(x == 0u64)]
fn old_in_modifying_loop_body_gated(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(*old(x) == *x);
        *x = 7u64;
        i += 1u64;
    }
}

// GATED: … also after the body's write.
#[trust_vc::requires(x == 0u64)]
fn old_after_write_in_loop_body_gated(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 7u64;
        trust_vc::assert!(*old(x) == 7u64);
        i += 1u64;
    }
}

// GATED (was a false Verified for an arbitrary entry): old() AFTER a loop
// with invariants that modified the param — its bare symbol is the post-loop
// state with the exit fact `!(x != 7)` assumed over it.
fn old_after_invariant_loop_gated(x: &mut u64) {
    while *x != 7u64 {
        trust_vc::invariant!(true);
        *x = 7u64;
    }
    trust_vc::assert!(*old(x) == 7u64);
}

// GATED (was a false Verified): the same shape in `ensures`.
#[trust_vc::ensures(*old(x) == 7u64)]
fn ensures_old_after_invariant_loop_gated(x: &mut u64) {
    while *x != 7u64 {
        trust_vc::invariant!(true);
        *x = 7u64;
    }
}
"#;

const LOOP_GATE: &str = "inside or after a loop that modifies";
const ENSURES_GATE: &str = "modified by a loop with invariants";

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

fn expect_gated(id: &str, func: &str, needle: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Error { message } if message.contains(needle) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needle:?}, got {other:?}")
        }
    }
}

#[test]
fn control_write_then_old_then_read_verifies() {
    expect_verified("c1", "write_then_old_then_read_verifies");
}

#[test]
fn liar_current_read_after_old_is_refuted() {
    expect_counterexample("l1", "current_read_after_old_liar");
}

#[test]
fn liar_old_reads_entry_not_current() {
    expect_counterexample("l2", "old_reads_entry_not_current_liar");
}

#[test]
fn control_old_before_write_then_read_verifies() {
    expect_verified("c2", "old_before_write_then_read_verifies");
}

#[test]
fn control_old_in_let_then_write_verifies() {
    expect_verified("c3", "old_in_let_then_write_verifies");
}

#[test]
fn control_old_rhs_write_verifies() {
    expect_verified("c4", "old_rhs_write_verifies");
}

#[test]
fn liar_old_rhs_wrong_relation_is_refuted() {
    expect_counterexample("l3", "old_rhs_wrong_relation_liar");
}

#[test]
fn control_alias_write_old_then_read_verifies() {
    expect_verified("c5", "alias_write_old_then_read_verifies");
}

#[test]
fn control_old_then_write_ensures_final_verifies() {
    expect_verified("c6", "old_then_write_ensures_final_verifies");
}

#[test]
fn control_compound_chain_then_old_verifies() {
    expect_verified("c7", "compound_chain_then_old_verifies");
}

#[test]
fn control_old_in_unmodifying_loop_body_verifies() {
    expect_verified("c8", "old_in_unmodifying_loop_body_verifies");
}

#[test]
fn control_old_after_no_invariant_loop_verifies() {
    expect_verified("c9", "old_after_no_invariant_loop_verifies");
}

#[test]
fn liar_old_after_no_invariant_loop_is_never_verified() {
    expect_never_verified("l4", "old_after_no_invariant_loop_liar");
}

#[test]
fn gated_old_in_modifying_loop_body() {
    expect_gated("g1", "old_in_modifying_loop_body_gated", LOOP_GATE);
}

#[test]
fn gated_old_after_write_in_loop_body() {
    expect_gated("g2", "old_after_write_in_loop_body_gated", LOOP_GATE);
}

#[test]
fn gated_old_after_invariant_loop() {
    expect_gated("g3", "old_after_invariant_loop_gated", LOOP_GATE);
}

#[test]
fn gated_ensures_old_after_invariant_loop() {
    expect_gated("g4", "ensures_old_after_invariant_loop_gated", ENSURES_GATE);
}
