// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 429 — bare `loop {}` with `break`): a regular
//! `invariant!` inside a guard-less loop is checked base + inductive-step
//! against the loop's OWN modified set, and the verified invariant facts are
//! available after the loop — exactly as they are for a `while` loop.
//!
//! Before this landed, `visit_expr_loop` pushed no loop context, so a bare
//! loop's invariant had no `loop_modified_vars` entry and its inductive step
//! fell into the havoc-ALL lane: every variable in the function was forgotten,
//! so even an invariant over UNMODIFIED state (`limit == 10`, with
//! `requires(limit == 10)`) refuted. The corpus pinned that as the
//! "basic_loop / loop2_ok_y non-tautological invariant current TrustVc gap"
//! counterexamples in `evals/verus/ported/loops.rs`.
//!
//! The liar cases are the point: a capability that verifies the true case but
//! cannot refute the false one is a rubber stamp. Two of the liars below are
//! SOUNDNESS guards that the missing context also left open (see the
//! `*_soundness` tests): without a registered modified set, a loop-modified
//! param fell back to its ENTRY symbol after the loop, and the body's
//! arithmetic was checked against the entry value instead of an arbitrary
//! loop-head value.
//!
//! Scope: the invariant must be INDEPENDENT of the loop-modified variables
//! whenever the body contains a `break`/`if` (the body is then non-flat, so no
//! single-iteration transition is captured and the inductive step havocs the
//! modified set). Invariants over the modified counter itself (upstream
//! `loop2_ok`'s `i == 0`) remain a genuine gap — rows 430/431 (break-site
//! checking + transition capture through `if { break }`), not this row.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_bli_{}_{}.rs", std::process::id(), tmp_id));
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

// Upstream `basic_loop` unmodified-state subset: the invariant mentions only
// `limit`, which the body never writes.
const UNMODIFIED_INVARIANT: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn unmodified_true(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == 10u64);
        i = 1u64;
        if i == 1u64 {
            break;
        }
    }
    trust_vc::assert!(limit == 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn unmodified_liar(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == 11u64);
        i = 1u64;
        if i == 1u64 {
            break;
        }
    }
    trust_vc::assert!(limit == 11u64);
}
"#;

// Upstream `loop2_ok_y` unmodified-state subset: labeled outer loop, labeled
// inner loop with `break 'y`, outer exit via `break 'x`.
const LABELED_NESTED: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn nested_true(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(limit == 10u64);
        i = 1u64;
        'y: loop {
            trust_vc::invariant!(limit == 10u64);
            break 'y;
        }
        if i == 1u64 {
            break 'x;
        }
    }
    trust_vc::assert!(limit == 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn nested_liar(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(limit == 10u64);
        i = 1u64;
        'y: loop {
            trust_vc::invariant!(limit == 9u64);
            break 'y;
        }
        if i == 1u64 {
            break 'x;
        }
    }
    trust_vc::assert!(limit == 10u64);
}
"#;

// A `let mut` counter (no VC var at entry) driving the bare loop.
const LETLOCAL_COUNTER: &str = r#"
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn letlocal_true(limit: u64) {
    let mut j = 0u64;
    loop {
        trust_vc::invariant!(limit == 10u64);
        j = 3u64;
        if j == 3u64 {
            break;
        }
    }
    trust_vc::assert!(limit == 10u64);
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
pub fn letlocal_liar(limit: u64) {
    let mut j = 0u64;
    loop {
        trust_vc::invariant!(limit == 10u64);
        j = 3u64;
        if j == 3u64 {
            break;
        }
    }
    trust_vc::assert!(j == 0u64);
}
"#;

// SOUNDNESS: a loop-modified PARAM must not keep its `requires` entry value
// after the loop. `i` is written in the body and read after it.
const STALE_ENTRY_READ: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn stale_entry_liar(mut i: u64) {
    loop {
        trust_vc::invariant!(true);
        i = 5u64;
        if i == 1u64 {
            break;
        }
    }
    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn stale_entry_liar_nontrivial_invariant(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == limit);
        i = 5u64;
        if i == 1u64 {
            break;
        }
    }
    trust_vc::assert!(i == 0u64);
}
"#;

// SOUNDNESS: body arithmetic over a loop-modified var is checked at an
// ARBITRARY loop head (under the invariants), not at the entry value. `x`
// starts at 0 but grows by 100 per iteration with no invariant bounding it, so
// `x + 100` can overflow — Verus reports exactly this. The control keeps the
// arithmetic over an UNMODIFIED operand (`limit`), which the invariant bounds.
const BODY_OVERFLOW: &str = r#"
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn body_overflow_liar(mut x: u64) {
    loop {
        trust_vc::invariant!(true);
        x = x + 100u64;
        if x > 1000u64 {
            break;
        }
    }
}

#[trust_vc::requires(limit <= 1000u64)]
#[trust_vc::ensures(true)]
pub fn body_arith_over_unmodified_operand_true(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit <= 1000u64);
        i = limit + 1u64;
        if i == 1u64 {
            break;
        }
    }
}
"#;

// Regression guards that must not move: a plain break reaches the following
// assertion, so `assert!(false)` after a bare loop refutes.
const BREAK_FALSE: &str = r#"
#[trust_vc::ensures(true)]
pub fn break_false() {
    loop {
        break;
    }
    trust_vc::assert!(false);
}
"#;

// Known incompleteness, pinned so a future change is noticed: with a `break`
// in the body the single-iteration transition is not captured, so an
// invariant over the modified counter itself cannot be proven inductive and
// fails closed (upstream `loop2_ok`'s `i == 0` shape). Rows 430/431 own it.
const COUNTER_INVARIANT_GAP: &str = r#"
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn counter_invariant(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 5u64);
        i = i + 1u64;
        if i == 5u64 {
            break;
        }
    }
    trust_vc::assert!(i <= 5u64);
}
"#;

#[test]
fn bare_loop_unmodified_state_invariant_verifies_and_is_available_after_the_loop() {
    let result = verify("unmod_t", "unmodified_true", UNMODIFIED_INVARIANT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "row 429: an unmodified-state invariant in a bare loop with break must verify \
         and reach the post-loop assertion: {result:?}"
    );
}

#[test]
fn bare_loop_false_invariant_refutes() {
    let result = verify("unmod_l", "unmodified_liar", UNMODIFIED_INVARIANT);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a false invariant (base case) must be refuted: {result:?}"
    );
}

#[test]
fn labeled_nested_bare_loops_unmodified_state_invariant_verifies() {
    let result = verify("nest_t", "nested_true", LABELED_NESTED);
    assert!(
        matches!(result, VerifyResult::Verified),
        "row 429 (loop2_ok_y subset): labeled nested bare loops with an \
         unmodified-state invariant must verify: {result:?}"
    );
}

#[test]
fn labeled_nested_bare_loops_inner_false_invariant_refutes() {
    let result = verify("nest_l", "nested_liar", LABELED_NESTED);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a false INNER invariant must be refuted: {result:?}"
    );
}

#[test]
fn bare_loop_with_let_local_counter_verifies_unmodified_state_invariant() {
    let result = verify("ll_t", "letlocal_true", LETLOCAL_COUNTER);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a `let mut` counter driving the bare loop must not block the invariant: {result:?}"
    );
}

#[test]
fn bare_loop_with_let_local_counter_forgets_the_counter_initializer() {
    let result = verify("ll_l", "letlocal_liar", LETLOCAL_COUNTER);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the let-local counter's initializer must not survive the loop: {result:?}"
    );
}

#[test]
fn bare_loop_modified_param_forgets_its_entry_value_soundness() {
    let result = verify("stale_l", "stale_entry_liar", STALE_ENTRY_READ);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "SOUNDNESS: a param written in a bare loop must not keep its `requires` value \
         after the loop: {result:?}"
    );
    let result = verify(
        "stale_l2",
        "stale_entry_liar_nontrivial_invariant",
        STALE_ENTRY_READ,
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "SOUNDNESS: same with a non-literal tautological invariant: {result:?}"
    );
}

#[test]
fn bare_loop_body_arithmetic_is_checked_at_an_arbitrary_loop_head_soundness() {
    let result = verify("ovf_l", "body_overflow_liar", BODY_OVERFLOW);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "SOUNDNESS: `x + 100` in a bare loop with no bound on `x` can overflow and must \
         be refuted, not checked against the entry value: {result:?}"
    );
}

#[test]
fn bare_loop_body_arithmetic_over_unmodified_operand_verifies() {
    let result = verify(
        "ovf_t",
        "body_arith_over_unmodified_operand_true",
        BODY_OVERFLOW,
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "arithmetic over an unmodified operand bounded by the invariant must verify \
         (no over-rejection from the body havoc): {result:?}"
    );
}

#[test]
fn bare_loop_break_reaches_the_following_assertion() {
    let result = verify("bf", "break_false", BREAK_FALSE);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "upstream loop_break_false: `assert!(false)` after `loop {{ break; }}` refutes: {result:?}"
    );
}

#[test]
fn bare_loop_invariant_over_the_modified_counter_stays_a_pinned_gap() {
    let result = verify("cgap", "counter_invariant", COUNTER_INVARIANT_GAP);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "rows 430/431: an invariant over the modified counter with a break in the body \
         is NOT expected to verify yet (no transition capture through `if {{ break }}`); \
         if this now verifies, re-score those rows and move this pin: {result:?}"
    );
}
