// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A loop `invariant!` over a LET-BOUND loop variable now VERIFIES (was
//! "unresolved variable"), with the entry value fed ONLY to the base case.
//!
//! `let mut i = 0; while i < n { invariant!(i <= n); i += 1 }` — pre-fix the
//! let-local `i` was scoped-string-only (no VC var) so the invariant failed to
//! lower. The fix declares each loop-modified, typable let-local as a VC var (so
//! the invariant/guard lower and the M4 transition activates) and registers its
//! pre-loop value as a per-invariant ENTRY assumption passed through the
//! base-case scoped slot — reaching the entry check but NEVER the inductive step
//! or post-loop lanes (both havoc the modified var).
//!
//! The soundness guards are the load-bearing part: the entry value must not leak
//! past the loop (`no_leak_*`) or into preservation (`inductive_step_havocs_*`),
//! and a false invariant must refute — a leak would be a false-verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_llc_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// CAPABILITY: valid invariant over a let-local counter + post-loop assert holds.
const VALID: &str = r#"
#[trust_vc::requires(n <= 100u32)]
#[trust_vc::ensures(true)]
fn t(n: u32) {
    let mut i: u32 = 0u32;
    while i < n { trust_vc::invariant!(i <= n); i = i + 1u32; }
    trust_vc::assert!(i == n);
}
"#;

// CAPABILITY (negative): a post-loop assert not implied by inv ∧ !guard refutes.
const POST_FALSE: &str = r#"
#[trust_vc::requires(n <= 100u32)]
#[trust_vc::ensures(true)]
fn t(n: u32) {
    let mut i: u32 = 0u32;
    while i < n { trust_vc::invariant!(i <= n); i = i + 1u32; }
    trust_vc::assert!(i == n + 1u32);
}
"#;

// SOUNDNESS: a false invariant (only true at entry) must refute at the step.
const FALSE_INV: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let mut i: u32 = 0u32;
    while i < 10u32 { trust_vc::invariant!(i < 3u32); i = i + 1u32; }
}
"#;

// SOUNDNESS (CARDINAL): the entry value must not leak past the loop. Post-loop
// `i` is 10 (havoc'd, constrained by inv ∧ !guard), NOT its pre-loop 0.
const NO_LEAK: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let mut i: u32 = 0u32;
    while i < 10u32 { trust_vc::invariant!(i <= 10u32); i = i + 1u32; }
    trust_vc::assert!(i == 0u32);
}
"#;

#[test]
fn valid_letlocal_invariant_verifies() {
    let r = verify("valid", VALID, "t");
    assert!(
        matches!(r, VerifyResult::Verified),
        "a valid `invariant!(i <= n)` over a `let mut i` counter (post-loop `i == n`) must \
         VERIFY (no 'unresolved variable `i`'); got: {r:?}"
    );
}

#[test]
fn post_loop_assert_not_implied_refutes() {
    let r = verify("post_false", POST_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "post-loop `i == n + 1` is not implied by `i <= n ∧ i >= n`; must refute; got: {r:?}"
    );
}

#[test]
fn false_letlocal_invariant_refutes_at_step() {
    let r = verify("false_inv", FALSE_INV, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `invariant!(i < 3)` holds at entry (i=0) but is NOT preserved; the inductive \
         step must havoc `i` and refute — a Verified means the entry value leaked into \
         preservation; got: {r:?}"
    );
}

#[test]
fn entry_value_does_not_leak_past_loop() {
    let r = verify("no_leak", NO_LEAK, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: post-loop `i` is its havoc'd exit value (10), NOT its pre-loop 0; \
         `assert!(i == 0)` must refute — a Verified means the entry assumption leaked past the \
         loop; got: {r:?}"
    );
}

// CAPABILITY: a let-local counter RETURNED as the result — `result` binds to the
// POST-loop value (the return binding is a PostLoopAssume, exempt from the
// post-loop pre-state rewrite), so `ensures(result == n)` holds.
const RETURN_VALID: &str = r#"
#[trust_vc::requires(n <= 100u32)]
#[trust_vc::ensures(result == n)]
fn t(n: u32) -> u32 {
    let mut i: u32 = 0u32;
    while i < n { trust_vc::invariant!(i <= n); i = i + 1u32; }
    i
}
"#;

// SOUNDNESS (CARDINAL): returning the modified counter (post-loop 10) with a FALSE
// postcondition `result == 0` must REFUTE — the return binding must reference the
// POST-loop value, never the pre-loop `i__pre == 0` (which would false-verify).
const RETURN_STALE_FALSE: &str = r#"
#[trust_vc::ensures(result == 0u32)]
fn t() -> u32 {
    let mut i: u32 = 0u32;
    while i < 10u32 { trust_vc::invariant!(i <= 10u32); i = i + 1u32; }
    i
}
"#;

#[test]
fn letlocal_returned_as_result_verifies() {
    let r = verify("ret_valid", RETURN_VALID, "t");
    assert!(
        matches!(r, VerifyResult::Verified),
        "a let-local counter returned as result must link to its POST-loop value, so \
         `ensures(result == n)` verifies; got: {r:?}"
    );
}

#[test]
fn returned_modified_counter_false_postcondition_refutes() {
    let r = verify("ret_stale", RETURN_STALE_FALSE, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: the return binding must reference the POST-loop counter (10), not its \
         pre-loop value 0; `ensures(result == 0)` must refute; got: {r:?}"
    );
}
