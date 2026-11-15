// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN: a branch path condition is read in the state
//! where it was pushed, never as a fact about the state of a loop entered
//! after it.
//!
//! A path condition is a string over bare names. Inside a loop body a
//! loop-modified variable's bare name means the loop's state (the extractor
//! invalidates it at body entry), so a condition pushed BEFORE that loop that
//! mentions the variable by its bare name speaks of a different state:
//!   * pushed in an OUTER loop body around a nested loop (`if j > 0 { while j
//!     > -10 { j = j - 1; … } }` inside a `while`), and
//!   * pushed before EVERY loop over a binding whose pre-loop rendering is
//!     still its bare name — a parameter (`fn f(mut j: i64) { if j > 0 { while
//!     j > -10 { j = j - 1; assert!(j >= -1); } } }`), a struct parameter, or a
//!     body local after an earlier loop havocked it.
//!
//! Both renderings conflated the two states — the bare one (a body `assert!`
//! whose head rendering is inconsistent, every call precondition) used one
//! bare name for both, and the head one (exec arithmetic) either substituted
//! the INNERMOST frame's head symbol into the outer condition or left the
//! pre-loop name bare and DEFERRED the overflow obligation — so the guard
//! constrained the loop state and a false claim, call precondition or
//! overflow check verified. Before the fix every `*_liar` below that is not
//! marked otherwise was `Verified`.
//!
//! Now every name a loop entered after the condition modifies is renamed to
//! what it denoted at the push (`rename_path_condition_across_loops`): the
//! head symbol of the innermost loop that was already active and modifies it,
//! or else a fresh unconstrained PRE-LOOP symbol — the pre-loop fact is
//! forgotten about the loop state, which is Verus's rule (only invariants
//! cross the loop head). A mentioned non-scalar binding (a `Vec`, a struct)
//! has no rename target: the condition is left out of an obligation (only
//! stronger) and makes a guarded assumption `true` (dropped). The controls show
//! the sound part of the guard is kept: a condition over a variable the loop
//! does NOT modify still guards the claim.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r#"
#[trust_vc::requires(x >= -1i64)]
#[trust_vc::ensures(true)]
fn need_ge_m1(x: i64) {}

// LIAR (bare lane on main): `j` passes `-1` in the inner loop, then
// `j - 1 == -2` reaches the claim.
#[trust_vc::ensures(true)]
fn outer_if_inner_loop_assert_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j > 0i64 {
            while j > -10i64 {
                j = j - 1i64;
                trust_vc::assert!(j >= -1i64);
            }
        }
        k = k + 1u64;
    }
}

// LIAR (a call precondition, always bare-rendered).
#[trust_vc::ensures(true)]
fn outer_if_inner_loop_call_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j > 0i64 {
            while j > -10i64 {
                j = j - 1i64;
                need_ge_m1(j);
            }
        }
        k = k + 1u64;
    }
}

// LIAR (exec arithmetic, the head lane): `n == 99` reaches `249 + 10`.
#[trust_vc::ensures(true)]
fn outer_if_inner_loop_overflow_liar(n: u8) {
    let mut j: u8 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j < 100u8 {
            while j < 250u8 {
                j = j + 10u8;
            }
        }
        k = k + 1u64;
    }
}

// LIAR (the break-site path condition): `j >= 0` holds BEFORE the inner loop
// only. It must stay a counterexample: that condition, read as a fact
// inside the inner loop, would make it verify.
#[trust_vc::ensures(true)]
fn outer_break_site_inner_loop_assert_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j < 0i64 {
            break;
        }
        while j > -10i64 {
            j = j - 1i64;
            trust_vc::assert!(j >= -1i64);
        }
        k = k + 1u64;
    }
}

// LIAR (the break-site path condition, the claim read through a body-local).
// Counterexample on main (no break-site path condition there).
#[trust_vc::ensures(true)]
fn outer_break_site_inner_loop_capture_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j < 0i64 {
            break;
        }
        while j > -10i64 {
            j = j - 1i64;
            let t = j;
            trust_vc::assert!(t >= -1i64);
        }
        k = k + 1u64;
    }
}

// LIAR (a claim AFTER the inner loop, same outer body): the `if` condition
// `j >= 0` holds before the inner loop only; the inner loop drives `j` to
// `-10`, so the claim is false whenever the branch is taken. Counterexample
// on main (the post-loop `j` is a fresh exit symbol); pinned with the three
// site-condition shapes below, which were Counterexample on main too.
#[trust_vc::ensures(true)]
fn outer_if_post_inner_loop_claim_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j >= 0i64 {
            while j > -10i64 {
                j = j - 1i64;
            }
            trust_vc::assert!(j >= 0i64);
        }
        k = k + 1u64;
    }
}

// LIAR (the break-site path condition, a claim AFTER the inner loop): `!(j <
// 0)` is a fact about `j` at the site, not after the inner loop.
#[trust_vc::ensures(true)]
fn outer_break_site_post_inner_loop_claim_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j < 0i64 {
            break;
        }
        while j > -10i64 {
            j = j - 1i64;
        }
        trust_vc::assert!(j >= 0i64);
        k = k + 1u64;
    }
}

// LIAR (the same, the inner loop leaving by `break`).
#[trust_vc::ensures(true)]
fn outer_break_site_post_inner_breaking_loop_claim_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if j < 0i64 {
            break;
        }
        while j > -10i64 {
            j = j - 1i64;
            if j == -5i64 {
                break;
            }
        }
        trust_vc::assert!(j >= 0i64);
        k = k + 1u64;
    }
}

// LIAR (the continue-site path condition, the variable updated after the
// site): `j == 3` passes the site and reaches `-2 >= 0`.
#[trust_vc::ensures(true)]
fn continue_site_then_update_claim_liar(n: i64) {
    let mut j: i64 = n;
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        k = k + 1u64;
        if j < 0i64 {
            continue;
        }
        j = j - 5i64;
        trust_vc::assert!(j >= 0i64);
    }
}

// ---------------- conditions pushed before every loop ----------------

#[trust_vc::requires(x >= -1i64)]
#[trust_vc::ensures(true)]
fn need_ge_m1_again(x: i64) {}

// LIAR (a parameter; the bare lane): `j` passes `-1`, then `-2` reaches the
// claim.
#[trust_vc::ensures(true)]
fn param_if_loop_assert_liar(mut j: i64) {
    if j > 0i64 {
        while j > -10i64 {
            j = j - 1i64;
            trust_vc::assert!(j >= -1i64);
        }
    }
}

// LIAR (a parameter; a call precondition).
#[trust_vc::ensures(true)]
fn param_if_loop_call_liar(mut j: i64) {
    if j > 0i64 {
        while j > -10i64 {
            j = j - 1i64;
            need_ge_m1_again(j);
        }
    }
}

// LIAR (a parameter; exec arithmetic, deferred on main): `99 → … → 249 + 10`.
#[trust_vc::ensures(true)]
fn param_if_loop_overflow_liar(mut j: u8) {
    if j < 100u8 {
        while j < 250u8 {
            j = j + 10u8;
        }
    }
}

// LIAR (a parameter; the condition from a `match` arm).
#[trust_vc::ensures(true)]
fn param_match_arm_loop_assert_liar(mut j: i64) {
    match j > 0i64 {
        true => {
            while j > -10i64 {
                j = j - 1i64;
                trust_vc::assert!(j >= -1i64);
            }
        }
        false => {}
    }
}

// LIAR (a parameter read at the loop head): the second iteration sees `7`.
#[trust_vc::ensures(true)]
fn param_if_loop_head_read_liar(mut j: u64) {
    let mut k: u64 = 0u64;
    if j < 5u64 {
        while k < 3u64 {
            trust_vc::invariant!(k <= 3u64);
            trust_vc::assert!(j < 5u64);
            j = 7u64;
            k = k + 1u64;
        }
    }
}

struct Counter {
    val: u64,
}

// LIAR (a struct parameter's field read at the loop head).
#[trust_vc::ensures(true)]
fn struct_param_if_loop_head_read_liar(mut c: Counter) {
    let mut k: u64 = 0u64;
    if c.val < 5u64 {
        while k < 3u64 {
            trust_vc::invariant!(k <= 3u64);
            trust_vc::assert!(c.val < 5u64);
            c.val = 7u64;
            k = k + 1u64;
        }
    }
}

// LIAR (a body local havocked by an earlier inner loop, so its rendering at
// the `if` is its bare name again): `n == 6` reaches `3 >= 4`.
#[trust_vc::ensures(true)]
fn havocked_local_if_nested_loop_assert_liar(n: u64) {
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        let mut t: u64 = n;
        let mut m: u64 = 0u64;
        while m < 2u64 {
            trust_vc::invariant!(m <= 2u64);
            m = m + 1u64;
            t = n;
        }
        if t > 5u64 {
            while t > 0u64 {
                t = t - 1u64;
                trust_vc::assert!(t >= 4u64);
            }
        }
        k = k + 1u64;
    }
}

// CONTROL: a pre-loop condition over an UNMODIFIED parameter still guards the
// body claim.
#[trust_vc::ensures(true)]
fn param_if_unmodified_var_guards_loop_claim(mut j: i64, c: i64) {
    if c > 0i64 {
        while j > -10i64 {
            j = j - 1i64;
            trust_vc::assert!(c > 0i64);
        }
    }
}

// CONTROL: a true body claim over the modified parameter still verifies.
#[trust_vc::ensures(true)]
fn param_if_loop_true_claim(mut j: i64) {
    if j > 0i64 {
        while j > -10i64 {
            j = j - 1i64;
            trust_vc::assert!(j >= -10i64);
        }
    }
}

// CONTROL: a condition over a variable the inner loop does not modify still
// guards the inner claim.
#[trust_vc::ensures(true)]
fn outer_if_unmodified_var_guards_inner_claim() {
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if k < 2u64 {
            let mut m: u64 = 0u64;
            while m < 3u64 {
                trust_vc::invariant!(m <= 3u64);
                m = m + 1u64;
                trust_vc::assert!(k < 2u64);
            }
        }
        k = k + 1u64;
    }
}

// LIAR for the control: `k == 1` passes the guard.
#[trust_vc::ensures(true)]
fn outer_if_unmodified_var_guards_inner_claim_liar() {
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(k <= 3u64);
        if k < 2u64 {
            let mut m: u64 = 0u64;
            while m < 3u64 {
                trust_vc::invariant!(m <= 3u64);
                m = m + 1u64;
                trust_vc::assert!(k < 1u64);
            }
        }
        k = k + 1u64;
    }
}

// CONTROL (one loop): an in-body branch condition over a modified variable
// still guards the claim at the same depth.
#[trust_vc::ensures(true)]
fn single_loop_if_branch_guards_claim(n: i64) {
    let mut j: i64 = n;
    while j > -10i64 {
        if j > 0i64 {
            j = j - 1i64;
            trust_vc::assert!(j >= 0i64);
        } else {
            j = j - 1i64;
        }
    }
}

// LIAR for the one-loop control: `j == 1` reaches `0 >= 1`.
#[trust_vc::ensures(true)]
fn single_loop_if_branch_guards_claim_liar(n: i64) {
    let mut j: i64 = n;
    while j > -10i64 {
        if j > 0i64 {
            j = j - 1i64;
            trust_vc::assert!(j >= 1i64);
        } else {
            j = j - 1i64;
        }
    }
}
"#;

fn verify(tmp_id: &str, func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_pcals_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, SRC).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

fn expect_verified(id: &str, func: &str) {
    match verify(id, func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn outer_branch_condition_is_not_read_at_the_inner_head() {
    expect_counterexample("l1", "outer_if_inner_loop_assert_liar");
    expect_counterexample("l2", "outer_if_inner_loop_call_liar");
    expect_counterexample("l3", "outer_if_inner_loop_overflow_liar");
}

#[test]
fn outer_break_site_condition_is_not_read_at_the_inner_head() {
    expect_counterexample("l4", "outer_break_site_inner_loop_assert_liar");
    expect_counterexample("l5", "outer_break_site_inner_loop_capture_liar");
}

#[test]
fn a_site_condition_is_not_read_after_a_later_update() {
    expect_counterexample("l8", "outer_if_post_inner_loop_claim_liar");
    expect_counterexample("l9", "outer_break_site_post_inner_loop_claim_liar");
    expect_counterexample(
        "l10",
        "outer_break_site_post_inner_breaking_loop_claim_liar",
    );
    expect_counterexample("l11", "continue_site_then_update_claim_liar");
}

#[test]
fn a_pre_loop_condition_is_not_read_as_a_fact_about_the_loop_state() {
    expect_counterexample("p1", "param_if_loop_assert_liar");
    expect_counterexample("p2", "param_if_loop_call_liar");
    expect_counterexample("p3", "param_if_loop_overflow_liar");
    expect_counterexample("p4", "param_match_arm_loop_assert_liar");
    expect_counterexample("p5", "param_if_loop_head_read_liar");
    expect_counterexample("p6", "struct_param_if_loop_head_read_liar");
    expect_counterexample("p7", "havocked_local_if_nested_loop_assert_liar");
    expect_verified("p8", "param_if_unmodified_var_guards_loop_claim");
    expect_verified("p9", "param_if_loop_true_claim");
}

#[test]
fn sound_guards_are_kept() {
    expect_verified("c1", "outer_if_unmodified_var_guards_inner_claim");
    expect_counterexample("l6", "outer_if_unmodified_var_guards_inner_claim_liar");
    expect_verified("c2", "single_loop_if_branch_guards_claim");
    expect_counterexample("l7", "single_loop_if_branch_guards_claim_liar");
}
