// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness regressions for two closure-body holes closed in
//! `body_extract.rs`:
//!
//! 1. INVOKED EXEC CLOSURE body panic-freedom (`let g = |x, y| x / y; g(a, b)`).
//!    The closure body's divide-by-zero / overflow / index bound was never lowered
//!    (the isolated-scope closure visit drops body effects), so a guaranteed
//!    runtime panic silently `Verified`. The fix instruments the body at the CALL
//!    site, substituting params with the call arguments, with the SAME reflexive
//!    arith-safety / index-bounds obligations the straight-line paths use.
//!
//!    CARDINAL exec-vs-spec discrimination: only a LOCAL-bound, then-CALLED closure
//!    is instrumented. A SPEC closure passed inline to `Seq::new`/`map`/… is an
//!    argument, never a `let`-bound-then-called local, so its ghost body is never
//!    instrumented — `Seq::new(n, |i| ((i + 1) as i32) * 10)` keeps verifying.
//!
//! 2. CROSS-CLOSURE captured-var contamination (#74 residual). A closure body
//!    `assume!` over a captured free var `n` leaked as a flat global hypothesis and
//!    discharged a SIBLING closure's `assert!` over the same `n`. The fix freshens
//!    each assume-bearing closure's captured free vars to per-closure-unique
//!    declared symbols, isolating siblings while preserving each closure's OWN
//!    `assume ⟹ assert` reasoning. An `assume!`-free closure is left untouched, so
//!    a contract depending on an outer fact about a capture still verifies.

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let item =
        find_function(&file, func).unwrap_or_else(|| panic!("fixture should define fn {func}"));
    extract_verification_conditions_with_file_context(&file, item)
        .map(|vc| vc.verify())
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        })
}

fn assert_not_verified(code: &str, func: &str, what: &str) {
    let v = verdict(code, func);
    assert_ne!(
        v,
        VerifyResult::Verified,
        "{what}: fn {func} must NOT verify (fail closed), got {v:?}"
    );
}

fn assert_verified(code: &str, func: &str, what: &str) {
    let v = verdict(code, func);
    assert_eq!(
        v,
        VerifyResult::Verified,
        "{what}: fn {func} must verify (no over-rejection), got {v:?}"
    );
}

// ── (1) invoked exec closure body arith-safety ───────────────────────────────

#[test]
fn invoked_exec_closure_div_by_zero_is_not_verified() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let g = |x: u64, y: u64| x / y;
            let _ = g(a, b);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let g = |x, y| x / y; g(a, b) — unguarded div-by-zero",
    );
}

#[test]
fn invoked_exec_closure_mul_overflow_is_not_verified() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, y: u64) {
            let g = |x: u64| x * y;
            let _ = g(a);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let g = |x| x * y; g(a) — unbounded multiplication overflow",
    );
}

#[test]
fn immediately_invoked_exec_closure_div_by_zero_is_not_verified() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = (|x: u64, y: u64| x / y)(a, b);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "(|x, y| x / y)(a, b) — immediately-invoked div-by-zero",
    );
}

#[test]
fn invoked_exec_closure_with_requires_guard_verifies() {
    // No over-rejection: a `requires(b != 0)` that makes the call SAFE still
    // verifies (the call args resolve in the caller's scope, where the precondition
    // is assumed).
    assert_verified(
        r#"
        #[trust_vc::requires(b != 0)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let g = |x: u64, y: u64| x / y;
            let _ = g(a, b);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(b != 0); g(a, b) — provably-safe call",
    );
}

#[test]
fn invoked_exec_closure_with_safe_literal_arg_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64) {
            let g = |x: u64, y: u64| x / y;
            let _ = g(a, 5);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "g(a, 5) — divisor literal is non-zero",
    );
}

#[test]
fn exec_closure_rebound_to_safe_op_still_verifies() {
    // After a safe div call, `g` is rebound to `+`; the stale div body must NOT be
    // re-instrumented at the second call (no over-rejection from a stale binding).
    assert_verified(
        r#"
        #[trust_vc::requires(b != 0)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut g = |x: u64, y: u64| x / y;
            let _ = g(a, b);
            g = |x: u64, y: u64| x + y;
            let _ = g(0, 0);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "rebound g = |x, y| x + y; g(0, 0) — stale div body not reused",
    );
}

// ── CARDINAL: spec closures are NEVER instrumented ───────────────────────────

#[test]
fn spec_closure_seq_new_multiply_still_verifies() {
    // The exact prior-attempt regression: a SPEC closure handed to `Seq::new` whose
    // ghost-index body multiplies must NOT receive an exec arith-safety obligation.
    assert_verified(
        r#"
        use trust_vc_types::Seq;
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let s = Seq::new(n, |i| ((i + 1) as i32) * 10);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "Seq::new(n, |i| ((i + 1) as i32) * 10) — spec closure untouched",
    );
}

#[test]
fn spec_closure_named_then_seq_new_still_verifies() {
    // A closure BOUND to a local but passed to `Seq::new` (NOT called as `g(args)`)
    // is a spec use — its ghost body must not be instrumented.
    assert_verified(
        r#"
        use trust_vc_types::Seq;
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let gen = |i: int| ((i + 1) as i32) * 10;
            let s = Seq::new(n, gen);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let gen = ...; Seq::new(n, gen) — named spec closure not instrumented",
    );
}

#[test]
fn spec_closure_seq_map_still_verifies() {
    assert_verified(
        r#"
        use trust_vc_types::Seq;
        #[trust_vc::ensures(true)]
        fn f(s: Seq<i32>) {
            let t = s.map(|j: int, x: i32| x * 10);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "s.map(|j, x| x * 10) — spec map closure not instrumented",
    );
}

// ── (2) cross-closure captured-var contamination (#74 residual) ──────────────

#[test]
fn sibling_closure_assume_does_not_discharge_other_assert() {
    // Closure `a`'s `assume!(n > 100)` must NOT discharge sibling `b`'s
    // `assert!(n > 50)` over the same captured `n` — a real false `Verified`.
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let a = |x: u64| { trust_vc::assume!(n > 100); x };
            let b = |y: u64| { trust_vc::assert!(n > 50); y };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "sibling closure assume leaking to a different closure's assert",
    );
}

#[test]
fn sibling_closure_assume_equality_does_not_leak() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let a = |x: u64| { trust_vc::assume!(n == 7); x };
            let b = |y: u64| { trust_vc::assert!(n == 7); y };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "sibling closure assume(n == 7) leaking to assert(n == 7)",
    );
}

#[test]
fn single_closure_own_assume_implies_assert_verifies() {
    // No over-rejection: a single closure's OWN `assume ⟹ assert` over a captured
    // var stays consistent under the per-closure freshening.
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let a = |x: u64| { trust_vc::assume!(n > 100); trust_vc::assert!(n > 50); x };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "single closure assume(n > 100) ⟹ assert(n > 50)",
    );
}

#[test]
fn two_self_contained_assume_closures_each_verify() {
    // Two siblings, each with its OWN assume⟹assert — both must verify; the
    // freshening keeps each closure's reasoning intact without cross-leak.
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let a = |x: u64| { trust_vc::assume!(n > 100); trust_vc::assert!(n > 50); x };
            let b = |y: u64| { trust_vc::assume!(n < 10); trust_vc::assert!(n < 20); y };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "two self-contained assume-bearing sibling closures",
    );
}

#[test]
fn assume_free_closure_keeps_outer_fact_dependency() {
    // No over-rejection: an `assume!`-free closure whose `assert!` legitimately
    // depends on the enclosing function's `requires(n > 0)` is NOT freshened, so the
    // outer fact still flows in.
    assert_verified(
        r#"
        #[trust_vc::requires(n > 0)]
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let a = |x: u64| { trust_vc::assert!(n > 0); x };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(n > 0); closure assert(n > 0) — outer fact preserved",
    );
}

#[test]
fn lone_closure_assert_over_arbitrary_capture_is_not_verified() {
    // Control: a closure-body `assert!` over an unconstrained captured var IS a real
    // obligation (so the contamination tests above are not vacuous).
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let b = |y: u64| { trust_vc::assert!(n == 7); y };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "lone closure assert(n == 7) over arbitrary n",
    );
}
