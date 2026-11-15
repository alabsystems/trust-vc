// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 430/431 — invariant and `loop_ensures` checks at
//! `break` sites; transition capture through break-only `if`s).
//!
//! A body of flat assignments plus `if cond { break; }` sites is now in the
//! exact-transition lane: the head-to-head inductive step assumes every site
//! fell through (`¬cond` conjoined into the guard), and each site emits exit
//! checks — every regular `invariant!` and every `loop_ensures!` must hold
//! there, proven as a frame-condition step under `guard ∧ cond` with the site's
//! transition. `invariant_except_break!` is not checked at exits. This is the
//! upstream `example_loop_break` family: before, a body with a `break` was pure
//! havoc, so an invariant over the loop counter could never be inductive and a
//! `loop_ensures` had to follow from the invariants alone.
//!
//! Every positive fixture pairs `invariant!(i <= 10)` with
//! `invariant_except_break!(i <= 9)`, as upstream does: with the break firing
//! at `i == 10`, the plain bound alone is NOT inductive (a head state with
//! `i == 10` satisfies it and steps to 11), and the engine rightly refutes it
//! — `invariant_not_preserved_on_the_fall_through_path_refutes` pins that.
//!
//! The liars are the point: a false invariant at a break site, a false
//! `ensures` at a break site, and an invariant that the fall-through path does
//! not preserve must all refute. An unconditional `break` (a body that never
//! reaches the head) stays out of the exact lane on purpose and keeps the
//! fail-closed havoc behavior (upstream `example_loop_break_fail3`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lbs_{}_{}.rs", std::process::id(), tmp_id));
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

// Upstream `example_loop_break` (u64 for the port's integer surface): the
// invariant bounds the counter, the except-break invariant is tighter, the
// ensures holds only at the break, and the post-loop assertion uses both.
const EXAMPLE_LOOP_BREAK: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_ensures_exact(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(i == 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i == 10u64);
}

#[trust_vc::requires(i == 10u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_fail1_ieb_false_at_entry(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_fail2_ieb_not_preserved(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 8u64);
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_fail3_immediate_break(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        break;
    }
    trust_vc::assert!(1u64 <= i);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn example_loop_break_fail4_post_loop_too_strong(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i <= 9u64);
}
"#;

const LIARS: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn invariant_false_at_break(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn ensures_false_at_break(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(i >= 11u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn invariant_not_preserved_on_fall_through(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 5u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn post_loop_fact_is_only_the_exit_fact(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i == 10u64);
}
"#;

// The same shape through a labeled bare loop, a `while` with a break-only site,
// and a `loop_decreases!` measure.
const VARIANTS: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn labeled_break_to_this_loop(mut i: u64) {
    'x: loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(i == 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break 'x;
        }
    }
    trust_vc::assert!(i == 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn while_with_break_site(mut i: u64) {
    while i < 100u64 {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i <= 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn while_with_break_site_no_normal_exit_fact(mut i: u64) {
    while i < 100u64 {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i >= 100u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn bare_loop_decreases_with_break_site(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
    trust_vc::assert!(i <= 10u64);
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
fn example_loop_break_verifies() {
    expect_verified(
        "example_loop_break",
        verify("elb", "example_loop_break", EXAMPLE_LOOP_BREAK),
    );
}

#[test]
fn example_loop_break_exact_ensures_reaches_post_loop() {
    expect_verified(
        "example_loop_break_ensures_exact",
        verify(
            "elbe",
            "example_loop_break_ensures_exact",
            EXAMPLE_LOOP_BREAK,
        ),
    );
}

#[test]
fn example_loop_break_fail1_refutes_an_except_break_invariant_false_at_entry() {
    expect_counterexample(
        "example_loop_break_fail1",
        verify(
            "elbf1",
            "example_loop_break_fail1_ieb_false_at_entry",
            EXAMPLE_LOOP_BREAK,
        ),
    );
}

#[test]
fn example_loop_break_fail2_refutes_an_except_break_invariant_not_preserved() {
    expect_counterexample(
        "example_loop_break_fail2",
        verify(
            "elbf2",
            "example_loop_break_fail2_ieb_not_preserved",
            EXAMPLE_LOOP_BREAK,
        ),
    );
}

#[test]
fn example_loop_break_fail3_immediate_break_refutes_the_ensures() {
    let result = verify(
        "elbf3",
        "example_loop_break_fail3_immediate_break",
        EXAMPLE_LOOP_BREAK,
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "an unconditional break stays in the havoc lane; `ensures 1 <= i` does not follow \
         from the invariant and must not verify: {result:?}"
    );
}

#[test]
fn example_loop_break_fail4_refutes_a_too_strong_post_loop_assertion() {
    expect_counterexample(
        "example_loop_break_fail4",
        verify(
            "elbf4",
            "example_loop_break_fail4_post_loop_too_strong",
            EXAMPLE_LOOP_BREAK,
        ),
    );
}

#[test]
fn invariant_false_at_the_break_site_refutes() {
    expect_counterexample(
        "invariant_false_at_break",
        verify("l1", "invariant_false_at_break", LIARS),
    );
}

#[test]
fn ensures_false_at_the_break_site_refutes() {
    expect_counterexample(
        "ensures_false_at_break",
        verify("l2", "ensures_false_at_break", LIARS),
    );
}

#[test]
fn invariant_not_preserved_on_the_fall_through_path_refutes() {
    expect_counterexample(
        "invariant_not_preserved_on_fall_through",
        verify("l3", "invariant_not_preserved_on_fall_through", LIARS),
    );
}

#[test]
fn post_loop_facts_are_only_the_checked_exit_predicates() {
    expect_counterexample(
        "post_loop_fact_is_only_the_exit_fact",
        verify("l4", "post_loop_fact_is_only_the_exit_fact", LIARS),
    );
}

#[test]
fn labeled_break_to_this_loop_is_an_exit_site() {
    expect_verified(
        "labeled_break_to_this_loop",
        verify("v1", "labeled_break_to_this_loop", VARIANTS),
    );
}

#[test]
fn while_with_a_break_site_verifies_its_invariant() {
    expect_verified(
        "while_with_break_site",
        verify("v2", "while_with_break_site", VARIANTS),
    );
}

#[test]
fn while_with_a_break_site_has_no_negated_guard_exit_fact() {
    expect_counterexample(
        "while_with_break_site_no_normal_exit_fact",
        verify("v3", "while_with_break_site_no_normal_exit_fact", VARIANTS),
    );
}

#[test]
fn bare_loop_decreases_with_a_break_site_verifies() {
    expect_verified(
        "bare_loop_decreases_with_break_site",
        verify("v4", "bare_loop_decreases_with_break_site", VARIANTS),
    );
}
