// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness regression for closures that capture-and-mutate an outer variable
//! (cluster P2).
//!
//! Before this fix, a closure body's assignment to a captured outer variable and
//! the closure's call sites were silently dropped (the body is visited in an
//! isolated scope that is reverted, and call effects are not modeled), so the
//! capture stayed FROZEN at its pre-closure value — and a stale-value claim
//! (`assert!(x == 0)` after `let mut x = 0; inc(); inc();` whose real `x == 2`)
//! falsely `Verified`. The closure may run any number of times with an unmodeled
//! effect, so `visit_expr_closure` now HAVOCS each captured-and-mutated variable
//! in the outer scope: a later read sees an arbitrary value, so the frozen
//! initializer is no longer provable (a sound, fail-closed outcome).

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

fn assert_not_verified(code: &str, func: &str) {
    let v = verdict(code, func);
    assert_ne!(
        v,
        VerifyResult::Verified,
        "fn {func} must NOT verify (capture mutation unmodeled — havoc/fail-closed expected), got {v:?}"
    );
}

#[test]
fn closure_captured_mutation_stale_local_is_not_verified() {
    // Real `x == 2` after two `inc()`; the frozen-initializer claim `x == 0` must
    // NOT verify.
    assert_not_verified(
        r#"
        fn f() {
            let mut x = 0u64;
            let mut inc = || { x = x + 1u64; };
            inc();
            inc();
            trust_vc::assert!(x == 0u64);
        }
        "#,
        "f",
    );
}

#[test]
fn closure_captured_mutation_other_stale_value_is_not_verified() {
    assert_not_verified(
        r#"
        fn f() {
            let mut x = 0u64;
            let mut inc = || { x = x + 1u64; };
            inc();
            trust_vc::assert!(x == 1u64);
        }
        "#,
        "f",
    );
}

#[test]
fn closure_captured_param_mutation_stale_entry_is_not_verified() {
    assert_not_verified(
        r#"
        #[trust_vc::requires(*p == start)]
        fn f(p: &mut u64, start: u64) {
            let mut inc = || { *p = *p + 1u64; };
            inc();
            inc();
            trust_vc::assert!(*p == start);
        }
        "#,
        "f",
    );
}

#[test]
fn direct_increment_without_closure_still_verifies_true_value() {
    // Control: the SAME arithmetic WITHOUT a closure must still be modeled
    // exactly (no over-rejection of the genuine straight-line case).
    assert_eq!(
        verdict(
            r#"
            fn f() {
                let mut x = 0u64;
                x = x + 1u64;
                x = x + 1u64;
                trust_vc::assert!(x == 2u64);
            }
            "#,
            "f",
        ),
        VerifyResult::Verified,
        "straight-line increments (no closure) must still verify the true value",
    );
}
