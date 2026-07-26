// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! M4 loop-body transition: end-to-end tests for the preservation
//! (inductive-step) VC.
//!
//! The inductive step is Hoare preservation `{I ∧ guard} body {I}`: the
//! loop-modified variables are havoc'd to ARBITRARY values constrained only by
//! the invariant and guard at the loop head (pre-state), the straight-line body
//! transition maps that arbitrary pre-state to the post-body state, and the
//! invariant must then hold on the post-body state.
//!
//! These tests go through `verify_function_from_file`, i.e. the real
//! source-extraction pipeline (`body_extract.rs` -> frame-condition inductive
//! step), exercising both the capture of the body transition and its
//! application in the inductive step.
//!
//! Soundness focus (the fail-closed cases below are the crux):
//!   * a FALSE invariant must NOT verify (not preserved),
//!   * an invariant-BREAKING body must produce a counterexample,
//!   * a post-loop assertion that does not follow from `inv ∧ !guard` must NOT
//!     verify,
//!   * a modified variable must NOT retain its pre-loop concrete value after the
//!     loop (proves the havoc is real — no pre-loop value leak).
//!
//! VERIFICATION LEVEL: VERIFY.

use std::fs;
use std::path::PathBuf;
use trust_vc_core::VerifyResult;

/// Writes `code` to a unique temp file and verifies the named function via the
/// full source-extraction + verification pipeline.
fn verify(test_name: &str, code: &str, func_name: &str) -> VerifyResult {
    let mut dir = std::env::temp_dir();
    dir.push(format!("trust_vc_m4_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    let file: PathBuf = dir.join("src.rs");
    fs::write(&file, code).unwrap();
    let result = trust_vc_core::verify_function_from_file(file.to_str().unwrap(), func_name)
        .expect("extraction/verification pipeline should not error");
    fs::remove_dir_all(&dir).ok();
    result
}

// ---------------------------------------------------------------------------
// POSITIVE: were incomplete before M4 (havoc with no body transition), now
// verify because the body transition is applied in the inductive step.
// ---------------------------------------------------------------------------

/// `while i < 10 { invariant!(i <= 10); i = i + 1 }; assert!(i == 10)`.
///
/// Inductive step: assume `i_pre <= 10 ∧ i_pre < 10`, apply `i = i_pre + 1`,
/// prove `i <= 10` (holds: `i_pre <= 9` so `i <= 10`). Post-loop: `!(i < 10)`
/// gives `i >= 10`, the invariant gives `i <= 10`, so `i == 10`.
#[test]
fn test_count_up_invariant_on_modified_var_verifies() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i <= 10)]
fn count_up(mut i: i32) {
    while i < 10 {
        trust_vc::invariant!(i <= 10);
        i = i + 1;
    }
    trust_vc::assert!(i == 10);
}
"#;
    let result = verify("count_up", code, "count_up");
    assert!(
        result.is_verified(),
        "count_up should verify via the loop-body transition, got: {result:?}"
    );
}

/// Accumulator loop whose invariant relates TWO modified variables.
///
/// `while i < n { invariant!(s == i); i = i + 1; s = s + 1 }`. Both `i` and `s`
/// are havoc'd; the inductive step needs BOTH body transitions
/// (`i == i_pre + 1`, `s == s_pre + 1`) to prove `s == i` from `s_pre == i_pre`.
#[test]
fn test_accumulator_two_modified_vars_verifies() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(s == i)]
fn accumulate(mut i: i32, n: i32, mut s: i32) {
    while i < n {
        trust_vc::invariant!(s == i);
        i = i + 1;
        s = s + 1;
    }
    trust_vc::assert!(s == i);
}
"#;
    let result = verify("accumulate", code, "accumulate");
    assert!(
        result.is_verified(),
        "two-modified-var accumulator invariant should verify, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// ADVERSARIAL: must FAIL CLOSED. These are the soundness crux — a missing
// havoc, a leaked pre-loop value, or a mis-encoded transition would turn any
// of these into a false `Verified`.
// ---------------------------------------------------------------------------

/// (a) FALSE invariant: `invariant!(i <= 5)` while the body grows `i`
/// unboundedly. The base case holds (`requires(i <= 5)`) but the step does NOT:
/// the havoc'd `i_pre = 5` (allowed by `i_pre <= 5`) plus `i = i_pre + 1` yields
/// `i = 6 > 5`.
///
/// The loop guard is on a SEPARATE counter `c` (not on `i`) so the post-loop
/// assumption set `i <= 5 ∧ c >= n` stays satisfiable; this keeps the failure
/// the inductive-step counterexample rather than a (also-sound but less precise)
/// vacuity rejection. A guard directly on `i` (e.g. `while i < 10`) makes the
/// post-loop state `i <= 5 ∧ i >= 10` contradictory, in which case the engine
/// fails closed with `Unknown{VacuousTruth}` instead — still NOT verified.
#[test]
fn test_false_invariant_not_preserved_fails_closed() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i <= 5)]
fn false_inv(mut i: i32, mut c: i32, n: i32) {
    while c < n {
        trust_vc::invariant!(i <= 5);
        i = i + 1;
        c = c + 1;
    }
}
"#;
    let result = verify("false_inv", code, "false_inv");
    assert!(
        result.is_counterexample(),
        "a false invariant must produce a counterexample (not preserved), got: {result:?}"
    );
}

/// (b) Invariant-BREAKING body: `invariant!(i <= n)` with body `i = i + 2`,
/// guard `i < n`. `i_pre = n - 1` (allowed by the guard) yields `i = n + 1 > n`.
#[test]
fn test_breaking_body_overshoots_fails_closed() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i <= n)]
fn overshoot(mut i: i32, n: i32) {
    while i < n {
        trust_vc::invariant!(i <= n);
        i = i + 2;
    }
}
"#;
    let result = verify("overshoot", code, "overshoot");
    assert!(
        result.is_counterexample(),
        "an invariant-breaking body must produce a counterexample, got: {result:?}"
    );
}

/// (c) Post-loop assertion that does NOT follow from `inv ∧ !guard`.
/// The invariant `i <= 10` is preserved (so the loop itself verifies), but
/// `inv ∧ !(i < 10)` gives `i == 10`, which refutes `assert!(i == 11)`.
#[test]
fn test_post_loop_assert_not_implied_fails_closed() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i <= 10)]
fn bad_post(mut i: i32) {
    while i < 10 {
        trust_vc::invariant!(i <= 10);
        i = i + 1;
    }
    trust_vc::assert!(i == 11);
}
"#;
    let result = verify("bad_post", code, "bad_post");
    assert!(
        !result.is_verified(),
        "a post-loop assertion not implied by inv & !guard must NOT verify, got: {result:?}"
    );
}

/// GATE: a conditional (non-flat) body must NOT be captured — it falls back to
/// pure havoc. This closes the stale-read false-Verified hole: with a body like
/// `if c { i = i + 1 }` a naive capture would read a stale loop-head `i` for any
/// later dependent assignment and could pin a transition that misses a real
/// post-state. Here the invariant `i <= n` is in fact PRESERVED (guard `i < n`
/// gives `i <= n-1`, so `i + 1 <= n` on the taken branch, and `i <= n` on the
/// skipped branch), yet because the body is not flat we capture nothing and the
/// inductive step havocs `i` — leaving the (true) invariant unproven. NOT
/// verified is the SOUND, conservative direction (incomplete, never unsound).
#[test]
fn test_conditional_body_falls_back_to_havoc_not_verified() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i <= n)]
fn cond_body(mut i: i32, n: i32, c: bool) {
    while i < n {
        trust_vc::invariant!(i <= n);
        if c {
            i = i + 1;
        }
    }
}
"#;
    let result = verify("cond_body", code, "cond_body");
    assert!(
        !result.is_verified(),
        "a conditional (non-flat) body must fall back to havoc (no transition captured); \
         capturing here would risk a false Verified, got: {result:?}"
    );
}

/// (d) Pre-loop value LEAK probe — the decisive havoc test.
/// `requires(i == 0)`, body `i = i + 1`. After the loop the modified `i` must
/// be its post-loop value (`i == 10`), NOT its pre-loop concrete value `0`. If
/// the havoc were unsound (current `i` leaked from the pre-loop entry value),
/// `assert!(i == 0)` would falsely verify.
#[test]
fn test_pre_loop_value_does_not_leak_fails_closed() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(i == 0)]
fn no_leak(mut i: i32) {
    while i < 10 {
        trust_vc::invariant!(i <= 10);
        i = i + 1;
    }
    trust_vc::assert!(i == 0);
}
"#;
    let result = verify("no_leak", code, "no_leak");
    assert!(
        !result.is_verified(),
        "modified var must not retain its pre-loop value after the loop (havoc must be real), \
         got: {result:?}"
    );
}
