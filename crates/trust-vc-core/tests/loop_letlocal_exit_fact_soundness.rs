// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CARDINAL soundness guard: the post-loop negated-guard exit fact must NOT leak
//! a STALE pre-loop value of an UNDECLARED loop-modified counter.
//!
//! A `let mut i = 0` loop counter is an UNDECLARED scoped-only local (no VC var).
//! In `visit_expr_while` the `guard` string is rendered PRE-loop, so for such a
//! counter it substitutes the initializer (`0`). In the HAS-INVARIANT branch the
//! exit fact `!(guard)` was added UNCONDITIONALLY, so `while i < n { invariant!(..);
//! i += 1 }` produced the FALSE post-loop fact `!(0 < n) == n <= 0`, wrongly
//! pinning `n == 0`:
//!
//!   fn f(n: usize) { let mut i = 0; while i < n { invariant!(n >= 0); i += 1 } assert!(n == 0); }
//!
//! false-Verified before the fix. The fix DROPS the exit fact when the guard
//! references an undeclared modified local (mirroring the no-invariant branch);
//! the fact is a dropped hypothesis (sound), and the counter is invalidated
//! anyway so no post-loop read could consume it through the counter.
//!
//! A DECLARED loop counter (a `mut i` param) keeps the fact — its bare symbol
//! carries no stale value — so genuine `assert!(i == n)`-style post-loop reasoning
//! is unaffected (pinned by `param_loop_still_reasons`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lef_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// The core false-verify: assert about a param `n` that the stale exit fact `n<=0`
// wrongly pinned. `n` is arbitrary usize, so `n == 0` is false.
const STALE_EXIT_PARAM: &str = r#"
#[trust_vc::ensures(true)]
fn f(n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(n >= 0usize);
        i = i + 1usize;
    }
    trust_vc::assert!(n == 0usize);
}
"#;

// Constant bound: `while i < 10` → stale `!(0 < 10) == false`; a false hypothesis
// must not verify `assert!(false)`.
const STALE_EXIT_CONST: &str = r#"
#[trust_vc::ensures(true)]
fn f(m: usize) {
    let mut i = 0usize;
    while i < 10usize {
        trust_vc::invariant!(m >= 0usize);
        i = i + 1usize;
    }
    trust_vc::assert!(m == 7usize);
}
"#;

// Two-variable guard `i < n` with the invariant about a THIRD param.
const STALE_EXIT_TWOVAR: &str = r#"
#[trust_vc::requires(k <= 3usize)]
#[trust_vc::ensures(true)]
fn f(n: usize, k: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(k <= 3usize);
        i = i + 1usize;
    }
    trust_vc::assert!(n == 0usize);
}
"#;

#[test]
fn stale_exit_fact_over_letlocal_counter_does_not_false_verify() {
    let r = verify("param", STALE_EXIT_PARAM, "f");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `assert!(n == 0)` after a `let mut i = 0; while i < n` loop must NOT verify \
         — the stale exit fact `!(0 < n)` must not leak; got: {r:?}"
    );
}

#[test]
fn stale_exit_fact_const_bound_does_not_false_verify() {
    let r = verify("const", STALE_EXIT_CONST, "f");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `assert!(m == 7)` (m arbitrary) after a const-bound let-local loop must NOT \
         verify via a stale/contradictory exit fact; got: {r:?}"
    );
}

#[test]
fn stale_exit_fact_twovar_guard_does_not_false_verify() {
    let r = verify("twovar", STALE_EXIT_TWOVAR, "f");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `assert!(n == 0)` after `while i < n` (let-local i) must NOT verify; got: {r:?}"
    );
}

// A DECLARED (param) loop counter must STILL let genuine post-loop reasoning
// through: `while i < 10` with `invariant!(i <= 10)` exits at `i == 10`.
const PARAM_LOOP: &str = r#"
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

#[test]
fn param_loop_still_reasons() {
    let r = verify("param_loop", PARAM_LOOP, "count_up");
    assert!(
        matches!(r, VerifyResult::Verified),
        "a DECLARED (param) loop counter keeps the exit fact, so `assert!(i == 10)` after \
         `while i < 10 {{ invariant!(i <= 10); i += 1 }}` must still VERIFY; got: {r:?}"
    );
}
