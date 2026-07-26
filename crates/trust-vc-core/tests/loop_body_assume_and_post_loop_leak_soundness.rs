// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// SOUNDNESS-CRITICAL: two more instances of the conditional/loop-scope fact-leak
// class already fixed for assume!-if/else (#67), call-ensures-if/else (#69) and
// call-ensures-loop (#70).
//
// LEAK A — a loop-body `assume!(P)` must NOT leak its raw `P` past the (possibly
// zero-trip) loop into a post-loop `assert!` or the function postcondition.
//
// LEAK B — a `while` loop's auto-generated normal-exit fact (the negated guard)
// must be (a) branch-guarded so a loop nested in `if c {..}` does not leak the
// fact into the sibling `else` or out as a postcondition, and (b) forward-ordered
// so an `assert!` textually BEFORE the loop is not retroactively satisfied.
//
// NON-NEGOTIABLE in the other direction: the legitimate STRAIGHT-LINE post-loop
// case (`while x<10 {..} assert!(x>=10)`) and a normal verified loop with an
// invariant MUST stay Verified, and an in-loop `assert!(false)` MUST stay a
// Counterexample (the loop body's OBLIGATIONS are not made vacuous).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ============ LEAK A: loop-body assume! must not leak past the loop ============

// `while c {}` may run zero times, so the body assume!(x==7) need not run; the
// post-loop assert!(x==7) on a free x must NOT verify.
fn leak_a_while(c: bool, x: u64) {
    while c { trust_vc::assume!(x == 7u64); }
    trust_vc::assert!(x == 7u64);
}

fn leak_a_for(n: u64, x: u64) {
    for _k in 0u64..n { trust_vc::assume!(x == 7u64); }
    trust_vc::assert!(x == 7u64);
}

fn leak_a_bare(c: bool, x: u64) {
    loop {
        if c { break; }
        trust_vc::assume!(x == 7u64);
        break;
    }
    trust_vc::assert!(x == 7u64);
}

fn leak_a_nested(n: u64, m: u64, x: u64) {
    let mut i = 0u64;
    while i < n {
        let mut j = 0u64;
        while j < m {
            trust_vc::assume!(x == 7u64);
            j = j + 1u64;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(x == 7u64);
}

// The headline catastrophe: a loop-body assume proving a false function
// postcondition.
#[trust_vc::ensures(x == 7u64)]
fn leak_a_postcondition(c: bool, x: u64) {
    while c { trust_vc::assume!(x == 7u64); }
}

// ============ LEAK B: post-loop normal-exit fact must be guarded + ordered ====

// Sibling-else: the loop's exit fact (`!(x<10)`) is established only on the `c`
// branch; the `else` arm must NOT see it.
fn leak_b_sibling_else(c: bool, mut x: u64) {
    if c {
        while x < 10u64 { x = x + 1u64; }
    } else {
        trust_vc::assert!(x >= 10u64);
    }
}

// Retroactive: an assert BEFORE the loop must not be satisfied by the loop's
// exit fact.
fn leak_b_retroactive(mut x: u64) {
    trust_vc::assert!(x >= 10u64);
    while x < 10u64 { x = x + 1u64; }
}

// Postcondition established under a conditional loop must not verify (the loop
// may not run when !c).
#[trust_vc::ensures(x >= 10u64)]
fn leak_b_postcondition_in_if(c: bool, mut x: u64) {
    if c {
        while x < 10u64 { x = x + 1u64; }
    }
}

// ============ DECISIVE controls: in-loop obligations NOT made vacuous =========

fn false_assert_in_while(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(false);
        i = i + 1u64;
    }
}

fn false_assert_in_for(n: u64) {
    for _k in 0u64..n {
        trust_vc::assert!(false);
    }
}

// A nested-if obligation in a loop over a FREE guard var stays a counterexample.
fn nested_if_in_loop_cex(n: u64, g: bool, a: u64) {
    let mut i = 0u64;
    while i < n {
        if g { trust_vc::assert!(a == 7u64); }
        i = i + 1u64;
    }
}

// Bonus LEAK-B variant: an IN-LOOP assert that depends on the negated guard
// (false inside the loop, where the guard holds) must NOT be satisfied by the
// loop's own post-loop exit fact. Pre-fix this was a latent false Verified.
fn in_loop_assert_uses_negated_guard(mut i: u64, n: u64) {
    while i < n {
        trust_vc::assert!(i >= n);
        i = i + 1u64;
    }
}

// ============ NO over-rejection: legitimate cases MUST stay Verified ==========

// The straight-line post-loop fact genuinely holds at the post-loop point.
fn straight_line_post_loop(mut x: u64) {
    while x < 10u64 { x = x + 1u64; }
    trust_vc::assert!(x >= 10u64);
}

// Two post-loop asserts after a top-level loop both see the negated-guard fact.
fn straight_line_post_loop_multi(mut x: u64) {
    while x < 10u64 { x = x + 1u64; }
    trust_vc::assert!(x >= 10u64);
    trust_vc::assert!(!(x < 10u64));
}

#[trust_vc::requires(n == 10u64)]
fn verified_invariant_loop(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i >= 10u64);
}

// A legitimate forward assume OUTSIDE any loop still works (FIX A only drops
// in-loop assumes).
fn forward_assume_outside_loop(x: u64) {
    trust_vc::assume!(x == 7u64);
    trust_vc::assert!(x == 7u64);
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_loop_body_assume_post_loop_leak");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn assert_not_verified(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NOT verify (loop-scope fact leak must be closed), got Verified"
    );
}

fn assert_counterexample(func: &str) {
    let r = run(func);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{func} must be a Counterexample (in-loop obligation not vacuous), got: {r:?}"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (no over-rejection of the legitimate case), got: {r:?}"
    );
}

// ── LEAK A: loop-body assume! does not leak past the loop ────────────────────
#[test]
fn leak_a_while_closed() {
    assert_not_verified("leak_a_while");
}
#[test]
fn leak_a_for_closed() {
    assert_not_verified("leak_a_for");
}
#[test]
fn leak_a_bare_loop_closed() {
    assert_not_verified("leak_a_bare");
}
#[test]
fn leak_a_nested_closed() {
    assert_not_verified("leak_a_nested");
}
#[test]
fn leak_a_postcondition_closed() {
    assert_not_verified("leak_a_postcondition");
}

// ── LEAK B: post-loop normal-exit fact guarded + ordered ─────────────────────
#[test]
fn leak_b_sibling_else_closed() {
    assert_not_verified("leak_b_sibling_else");
}
#[test]
fn leak_b_retroactive_closed() {
    assert_not_verified("leak_b_retroactive");
}
#[test]
fn leak_b_postcondition_in_if_closed() {
    assert_not_verified("leak_b_postcondition_in_if");
}

// ── In-loop obligations NOT made vacuous ─────────────────────────────────────
#[test]
fn false_assert_in_while_still_cex() {
    assert_counterexample("false_assert_in_while");
}
#[test]
fn false_assert_in_for_still_cex() {
    assert_counterexample("false_assert_in_for");
}
#[test]
fn nested_if_in_loop_still_cex() {
    assert_counterexample("nested_if_in_loop_cex");
}
#[test]
fn in_loop_assert_using_negated_guard_still_cex() {
    assert_counterexample("in_loop_assert_uses_negated_guard");
}

// ── NO over-rejection ────────────────────────────────────────────────────────
#[test]
fn straight_line_post_loop_verifies() {
    assert_verified("straight_line_post_loop");
}
#[test]
fn straight_line_post_loop_multi_verifies() {
    assert_verified("straight_line_post_loop_multi");
}
#[test]
fn verified_invariant_loop_verifies() {
    assert_verified("verified_invariant_loop");
}
#[test]
fn forward_assume_outside_loop_verifies() {
    assert_verified("forward_assume_outside_loop");
}
