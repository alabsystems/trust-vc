// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 430/431 — `continue` paths): a continue-only
//! `if cond { continue; }` keeps the body in the exact-transition lane. At the
//! site EVERY invariant (regular and except-break) must be re-established and
//! every `loop_decreases!` measure must have strictly decreased, each proven
//! as a frame-condition step under `guard ∧ cond` with the site transition;
//! the fall-through head-to-head step assumes `¬cond`. A predicate proven at
//! a continue site is NOT a post-loop fact.
//!
//! This is upstream `example_loop_continue` / `example_loop_continue_fail`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lcs_{}_{}.rs", std::process::id(), tmp_id));
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
// Upstream example_loop_continue (u64): continue at 5, break at 10.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_continue(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);
        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 5u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream example_loop_continue_fail: the continue fires at i == 10, where the
// except-break invariant `i <= 9` is violated on the way back to the head.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_continue_fail(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);
        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// The measure must decrease on the continue path too: `i` is reset there, so
// `10 - i` grows back and WF2 must refute.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn measure_not_decreasing_on_continue(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);
        i = i + 1u64;
        if i == 5u64 {
            i = 0u64;
        }
        if i == 5u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }
}

// An except-break invariant proven at the continue site is NOT a post-loop
// fact: after the break at 10, `i <= 9` is false.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn continue_check_is_not_a_post_loop_fact(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        if i == 5u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i <= 9u64);
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
fn example_loop_continue_verifies() {
    expect_verified(
        "example_loop_continue",
        verify("elc", "example_loop_continue", SRC),
    );
}

#[test]
fn example_loop_continue_fail_refutes_the_except_break_invariant_at_the_continue() {
    expect_counterexample(
        "example_loop_continue_fail",
        verify("elcf", "example_loop_continue_fail", SRC),
    );
}

#[test]
fn a_measure_that_does_not_decrease_on_the_continue_path_does_not_verify() {
    let result = verify("mnd", "measure_not_decreasing_on_continue", SRC);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "the strict-descent copy at the continue site must refuse: {result:?}"
    );
}

#[test]
fn a_continue_site_check_is_not_a_post_loop_fact() {
    expect_counterexample(
        "continue_check_is_not_a_post_loop_fact",
        verify("cnp", "continue_check_is_not_a_post_loop_fact", SRC),
    );
}
