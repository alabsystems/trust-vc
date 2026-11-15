// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (post-loop facts are scoped to where they hold, measured
//! 2026-09-10): a post-loop fact — a `while`'s normal-exit `!(guard)` or the
//! unreachable marker after an infinite `loop {}` — emitted INSIDE an enclosing
//! loop body, a let-else diverge arm, or an unguardable `match` arm is DROPPED,
//! because those reachability conditions are not on the path stack and the
//! fact would otherwise be assumed after the enclosing construct on paths that
//! never established it. Three liars verified before this pin; the controls
//! keep the straight-line facts.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_plfs_{}_{}.rs", std::process::id(), tmp_id));
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
// LIAR: the inner while's exit fact `!(g)` escaped past the OUTER loop, which
// exits through `break` before reaching the inner loop when `c` holds.
#[trust_vc::ensures(true)]
pub fn inner_while_exit_fact_must_not_escape_outer_loop(c: bool, g: bool) {
    loop {
        trust_vc::invariant!(true);
        if c {
            break;
        }
        while g {
            trust_vc::invariant!(true);
        }
    }
    trust_vc::assert!(!g);
}

// LIAR: the unreachable marker of an inner infinite loop, same shape.
#[trust_vc::ensures(true)]
pub fn inner_infinite_loop_marker_must_not_escape_outer_loop(c: bool) {
    loop {
        trust_vc::invariant!(true);
        if c {
            break;
        }
        loop {}
    }
    trust_vc::assert!(false);
}

// LIAR (upstream let_else_just_a_normal_var::test_fails): the diverging arm of
// a let-else never runs for an irrefutable pattern.
#[trust_vc::ensures(true)]
pub fn let_else_diverge_arm_infinite_loop_is_dead(x: u64) {
    let _y = x else {
        loop {}
    };
    trust_vc::assert!(false);
}

// LIAR: a refutable let-else — the code after it runs when the pattern matched.
#[trust_vc::ensures(true)]
pub fn let_else_diverge_arm_marker_does_not_leak(o: Option<u64>) {
    let Some(x) = o else {
        loop {}
    };
    trust_vc::assert!(x == 5u64);
}

// CONTROL: a straight-line while keeps its normal-exit fact.
#[trust_vc::ensures(true)]
pub fn straight_line_while_keeps_exit_fact(g: bool) {
    while g {
        trust_vc::invariant!(true);
    }
    trust_vc::assert!(!g);
}

// CONTROL: a let-else whose arm returns still binds the matched value after it.
#[trust_vc::ensures(true)]
pub fn let_else_binding_after_returning_arm(o: Option<u64>) {
    let Some(x) = o else {
        return;
    };
    trust_vc::assert!(x == x);
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
fn liar_inner_while_exit_fact_must_not_escape_outer_loop() {
    expect_counterexample("l1", "inner_while_exit_fact_must_not_escape_outer_loop");
}

#[test]
fn liar_inner_infinite_loop_marker_must_not_escape_outer_loop() {
    expect_counterexample(
        "l2",
        "inner_infinite_loop_marker_must_not_escape_outer_loop",
    );
}

#[test]
fn liar_let_else_diverge_arm_infinite_loop_is_dead() {
    expect_counterexample("l3", "let_else_diverge_arm_infinite_loop_is_dead");
}

#[test]
fn liar_let_else_diverge_arm_marker_does_not_leak() {
    expect_counterexample("l4", "let_else_diverge_arm_marker_does_not_leak");
}

#[test]
fn control_straight_line_while_keeps_exit_fact() {
    expect_verified("c1", "straight_line_while_keeps_exit_fact");
}

#[test]
fn control_let_else_binding_after_returning_arm() {
    expect_verified("c2", "let_else_binding_after_returning_arm");
}
