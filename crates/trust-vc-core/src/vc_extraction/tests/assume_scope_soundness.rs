// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// SOUNDNESS-CRITICAL: body `assume!(P)` must be (1) branch-guarded — a
// branch-local assume must not leak into sibling/post-branch/dead-branch code
// or out as a function contract — and (2) forward-only — an `assert!` must be
// verified against only the assumes established at an EARLIER program point,
// never a later one (no retroactive satisfaction).

use super::*;
use crate::encoder::VerifyResult;

fn verify(code: &str, func_name: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let func = find_function(&file, func_name).unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    vc.verify()
}

fn is_verified(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Verified)
}

fn is_counterexample(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Counterexample { .. })
}

// ── Direction (i): NO false Verified ────────────────────────────────────────

#[test]
fn assert_before_assume_is_not_retroactively_satisfied() {
    // `assert!(b); assume!(b)` — the later assume must NOT satisfy the earlier
    // assert. This is the catastrophic retroactive case.
    let code = r#"
        fn f(b: bool) {
            trust_vc::assert!(b);
            trust_vc::assume!(b);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "assert!(b) before assume!(b) must NOT verify (retroactive satisfaction), got: {result:?}"
    );
}

#[test]
fn bare_assert_without_assume_is_counterexample_control() {
    // Control: the same assert WITHOUT any assume is a counterexample.
    let code = r#"
        fn f(b: bool) {
            trust_vc::assert!(b);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "bare assert!(b) on a free bool must be a counterexample, got: {result:?}"
    );
}

#[test]
fn branch_local_assume_does_not_leak_to_post_branch_assert() {
    let code = r#"
        fn f(b: bool, x: u64) {
            if b {
                trust_vc::assume!(x == 0u64);
            }
            trust_vc::assert!(x == 0u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "branch-local assume!(x==0) must NOT leak to a post-branch assert, got: {result:?}"
    );
}

#[test]
fn branch_local_assume_does_not_leak_to_sibling_else_assert() {
    let code = r#"
        fn f(b: bool, x: u64) {
            if b {
                trust_vc::assume!(x == 0u64);
            } else {
                trust_vc::assert!(x == 0u64);
            }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "branch-local assume!(x==0) must NOT leak into the sibling else branch, got: {result:?}"
    );
}

#[test]
fn dead_if_false_assume_has_no_effect() {
    // A statically dead `if false { assume!(P) }` must not establish P anywhere.
    let code = r#"
        fn f(x: u64) {
            if false {
                trust_vc::assume!(x == 0u64);
            }
            trust_vc::assert!(x == 0u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "a dead `if false {{ assume!(x==0) }}` must have no effect, got: {result:?}"
    );
}

#[test]
fn false_ensures_via_branch_local_assume_is_not_verified() {
    // The headline catastrophe: a branch-local assume proving a false function
    // postcondition.
    let code = r#"
        #[trust_vc::ensures(x == 0u64)]
        fn f(b: bool, x: u64) {
            if b {
                trust_vc::assume!(x == 0u64);
            }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        !is_verified(&result),
        "a false `ensures(x==0)` must NOT be proven by a branch-local assume, got: {result:?}"
    );
}

// ── Direction (ii): NO over-rejection (legitimate forward assumes work) ──────

#[test]
fn forward_assume_entails_later_assert_verifies() {
    // `assume!(P); assert!(Q)` where P entails Q.
    let code = r#"
        fn f(x: u64) {
            trust_vc::assume!(x == 0u64);
            trust_vc::assert!(x <= 0u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_verified(&result),
        "a legitimate forward assume!(x==0); assert!(x<=0) must verify, got: {result:?}"
    );
}

#[test]
fn unconditional_top_level_forward_assume_verifies() {
    let code = r#"
        fn f(x: u64) {
            trust_vc::assume!(x == 0u64);
            trust_vc::assert!(x == 0u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_verified(&result),
        "top-level assume!(x==0); assert!(x==0) must verify, got: {result:?}"
    );
}

#[test]
fn same_branch_forward_assume_then_assert_verifies() {
    let code = r#"
        fn f(b: bool, x: u64) {
            if b {
                trust_vc::assume!(x == 0u64);
                trust_vc::assert!(x == 0u64);
            }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_verified(&result),
        "same-branch forward assume+assert must verify, got: {result:?}"
    );
}

#[test]
fn forward_assume_false_is_vacuous_not_verified() {
    // assume!(false) in its own forward scope is vacuous → Unknown, not a clean
    // Verified (the existing vacuity gate owns this; we just must not regress it
    // into a false Verified or spurious counterexample).
    let code = r#"
        fn f(x: u64) {
            trust_vc::assume!(false);
            trust_vc::assert!(x == 1u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        !is_counterexample(&result),
        "assume!(false) forward scope must not produce a counterexample, got: {result:?}"
    );
    assert!(
        !is_verified(&result),
        "assume!(false) must be downgraded to Unknown(vacuous), not Verified, got: {result:?}"
    );
}

// ── LEAK A: a loop-body assume! must not leak past the (zero-trip) loop ───────

#[test]
fn loop_body_assume_does_not_leak_to_post_while_assert() {
    // `while c {}` may run zero times, so the body assume!(x==7) may never run;
    // the post-loop assert!(x==7) on a free x must NOT verify.
    let code = r#"
        fn f(c: bool, x: u64) {
            while c { trust_vc::assume!(x == 7u64); }
            trust_vc::assert!(x == 7u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "loop-body assume!(x==7) must NOT leak to a post-while assert, got: {result:?}"
    );
}

#[test]
fn loop_body_assume_does_not_leak_to_post_for_assert() {
    let code = r#"
        fn f(n: u64, x: u64) {
            for _k in 0u64..n { trust_vc::assume!(x == 7u64); }
            trust_vc::assert!(x == 7u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "loop-body assume!(x==7) must NOT leak to a post-for assert, got: {result:?}"
    );
}

#[test]
fn loop_body_assume_does_not_leak_to_postcondition() {
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn f(c: bool, x: u64) {
            while c { trust_vc::assume!(x == 7u64); }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        !is_verified(&result),
        "a false ensures(x==7) must NOT be proven by a loop-body assume, got: {result:?}"
    );
}

#[test]
fn false_assert_in_loop_stays_counterexample() {
    // The loop body's OBLIGATIONS are NOT made vacuous by dropping its assumes.
    let code = r#"
        fn f(n: u64) {
            let mut i = 0u64;
            while i < n {
                trust_vc::assert!(false);
                i = i + 1u64;
            }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "assert!(false) inside a loop must stay a counterexample, got: {result:?}"
    );
}

// ── LEAK B: a while loop's normal-exit fact must be guarded + forward-ordered ─

#[test]
fn post_loop_exit_fact_does_not_leak_to_sibling_else() {
    let code = r#"
        fn f(c: bool, mut x: u64) {
            if c {
                while x < 10u64 { x = x + 1u64; }
            } else {
                trust_vc::assert!(x >= 10u64);
            }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "a conditional loop's exit fact must NOT leak into the sibling else, got: {result:?}"
    );
}

#[test]
fn post_loop_exit_fact_does_not_satisfy_earlier_assert() {
    let code = r#"
        fn f(mut x: u64) {
            trust_vc::assert!(x >= 10u64);
            while x < 10u64 { x = x + 1u64; }
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_counterexample(&result),
        "an assert BEFORE a loop must NOT be retroactively satisfied by the exit fact, got: {result:?}"
    );
}

#[test]
fn straight_line_post_loop_exit_fact_still_verifies() {
    // NO over-rejection: a top-level loop's negated-guard exit fact genuinely
    // holds at the straight-line post-loop point.
    let code = r#"
        fn f(mut x: u64) {
            while x < 10u64 { x = x + 1u64; }
            trust_vc::assert!(x >= 10u64);
        }
    "#;
    let result = verify(code, "f");
    assert!(
        is_verified(&result),
        "straight-line post-loop assert!(x>=10) must still verify, got: {result:?}"
    );
}
