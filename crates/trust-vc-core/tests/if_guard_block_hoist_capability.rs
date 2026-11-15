// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (2026-09-11): an `if` whose guard is a BLOCK with a side
//! effect (`if { x += 1; x == 1 } { … } else { … }`) has the block's
//! statements hoisted in front of the `if` (`while_guard_desugar::hoist_if_guard`),
//! so the side effect is ordinary straight-line code and the branch condition
//! is the plain tail. Before, the whole block was rendered as the path
//! condition and the extraction failed closed on the compound assignment
//! (`tests/diverging_if_panic.rs::side_effecting_guard_once`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_igbh_{}_{}.rs", std::process::id(), tmp_id));
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
// CONTROL: the guard mutates x exactly once; the then-branch is taken.
#[trust_vc::ensures(result == 1u64)]
fn side_effecting_guard_once() -> u64 {
    let mut x = 0u64;
    if { x += 1u64; x == 1u64 } { 1u64 } else { 2u64 }
}

// LIAR: the else-branch is not taken.
#[trust_vc::ensures(result == 2u64)]
fn side_effecting_guard_once_liar() -> u64 {
    let mut x = 0u64;
    if { x += 1u64; x == 1u64 } { 1u64 } else { 2u64 }
}

// CONTROL: the hoisted effect is visible after the `if`.
#[trust_vc::ensures(true)]
fn guard_effect_persists() {
    let mut x = 0u64;
    let y = if { x += 1u64; x == 1u64 } { 10u64 } else { 20u64 };
    trust_vc::assert!(x == 1u64);
    trust_vc::assert!(y == 10u64);
}

// LIAR: … and it happened exactly once.
#[trust_vc::ensures(true)]
fn guard_effect_persists_liar() {
    let mut x = 0u64;
    let _y = if { x += 1u64; x == 1u64 } { 10u64 } else { 20u64 };
    trust_vc::assert!(x == 2u64);
}

// FAIL-CLOSED: an `else if` guard block sits in expression position (inside the
// `else`), where no enclosing statement can take the hoisted statements — it
// keeps the old refusal.
#[trust_vc::ensures(result == 3u64)]
fn else_if_guard_block() -> u64 {
    let mut x = 0u64;
    if x == 5u64 { 1u64 } else if { x += 3u64; x == 3u64 } { 3u64 } else { 4u64 }
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
fn control_side_effecting_guard_once_verifies() {
    expect_verified("c1", "side_effecting_guard_once");
}

#[test]
fn liar_side_effecting_guard_once_is_rejected() {
    expect_counterexample("l1", "side_effecting_guard_once_liar");
}

#[test]
fn control_guard_effect_persists_verifies() {
    expect_verified("c2", "guard_effect_persists");
}

#[test]
fn liar_guard_effect_persists_is_rejected() {
    expect_counterexample("l2", "guard_effect_persists_liar");
}

#[test]
fn else_if_guard_block_stays_fail_closed() {
    match verify("f1", "else_if_guard_block", SRC) {
        VerifyResult::Error { message } if message.contains("compound assignment") => {}
        other => {
            panic!("else_if_guard_block: expected the compound-assignment refusal, got {other:?}")
        }
    }
}
