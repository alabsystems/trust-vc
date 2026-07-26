// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// SOUNDNESS-CRITICAL: a conditionally-executed call's `ensures` must be (1)
// branch-guarded — a branch-local call's postcondition must not leak into
// sibling/post-branch/dead-branch code or out as a function contract — and (2)
// forward-only — an `assert!` textually BEFORE the call must not be satisfied
// by the call's `ensures` (no retroactive satisfaction). Its caller-side
// `requires` must be branch-guarded too, so a valid call whose precondition is
// implied by the enclosing branch guard is not over-rejected.

use super::*;
use crate::encoder::VerifyResult;

fn verify_with_context(code: &str, func_name: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let func = find_function(&file, func_name).unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    vc.verify()
}

fn is_verified(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Verified)
}

fn is_counterexample(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Counterexample { .. })
}

// ── Direction (i): NO false Verified (the catastrophe) ───────────────────────

#[test]
fn branch_local_call_ensures_does_not_leak_to_post_branch_assert() {
    // mk's ensures(x==7) holds only when mk(a) actually runs. Under `if c`, when
    // !c the call never runs, so the post-branch assert!(a==7) must NOT verify.
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn leak(c: bool, a: u64) {
            if c {
                let _ = mk(a);
            }
            trust_vc::assert!(a == 7u64);
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        is_counterexample(&result),
        "branch-local call ensures(x==7) must NOT leak to a post-branch assert, got: {result:?}"
    );
}

#[test]
fn branch_local_call_ensures_does_not_leak_to_sibling_else_assert() {
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn leak(c: bool, a: u64) {
            if c {
                let _ = mk(a);
            } else {
                trust_vc::assert!(a == 7u64);
            }
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        is_counterexample(&result),
        "branch-local call ensures(x==7) must NOT leak into the sibling else branch, got: {result:?}"
    );
}

#[test]
fn dead_if_false_call_ensures_has_no_effect() {
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn leak(a: u64) {
            if false {
                let _ = mk(a);
            }
            trust_vc::assert!(a == 7u64);
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        is_counterexample(&result),
        "a dead `if false {{ mk(a) }}` call ensures must have no effect, got: {result:?}"
    );
}

#[test]
fn branch_local_external_body_call_ensures_does_not_leak() {
    // The clean real-world exploit: #[external_body] trusted FFI helper whose
    // body is opaque. Its ensures is assumed; under `if c` it still must not leak.
    let code = r#"
        #[trust_vc::external_body]
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn leak(c: bool, a: u64) {
            if c {
                let _ = mk(a);
            }
            trust_vc::assert!(a == 7u64);
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        is_counterexample(&result),
        "external_body branch-local call ensures must NOT leak post-branch, got: {result:?}"
    );
}

#[test]
fn call_ensures_is_not_retroactively_satisfied() {
    // assert!(a==7) textually BEFORE the call must NOT be satisfied by the later
    // call's ensures, even when the call is unconditional.
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn retro(a: u64) {
            trust_vc::assert!(a == 7u64);
            let _ = mk(a);
        }
    "#;
    let result = verify_with_context(code, "retro");
    assert!(
        is_counterexample(&result),
        "assert!(a==7) before mk(a) must NOT be satisfied by the later call ensures, got: {result:?}"
    );
}

#[test]
fn false_ensures_via_branch_local_call_is_not_verified() {
    // The headline catastrophe on the POSTCONDITION path (which keeps every
    // assumption unconditionally): a branch-local call must NOT prove a false
    // whole-function postcondition. When !c, mk(a) never runs, so ensures(a==7)
    // is false.
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        #[trust_vc::ensures(a == 7u64)]
        fn leak(c: bool, a: u64) {
            if c {
                let _ = mk(a);
            }
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        !is_verified(&result),
        "a false ensures(a==7) must NOT be proven by a branch-local call ensures, got: {result:?}"
    );
}

#[test]
fn false_ensures_via_branch_local_external_body_call_is_not_verified() {
    let code = r#"
        #[trust_vc::external_body]
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        #[trust_vc::ensures(a == 7u64)]
        fn leak(c: bool, a: u64) {
            if c {
                let _ = mk(a);
            }
        }
    "#;
    let result = verify_with_context(code, "leak");
    assert!(
        !is_verified(&result),
        "external_body branch-local call must NOT prove a false function ensures, got: {result:?}"
    );
}

#[test]
fn unconditional_call_ensures_proves_true_function_ensures() {
    // No over-rejection on the postcondition path: an UNCONDITIONAL call's
    // ensures legitimately establishes a matching function postcondition.
    let code = r#"
        #[trust_vc::ensures(result == x)]
        fn id(x: u64) -> u64 { x }

        #[trust_vc::ensures(result == a)]
        fn good(a: u64) -> u64 {
            id(a)
        }
    "#;
    let result = verify_with_context(code, "good");
    assert!(
        is_verified(&result),
        "an unconditional call ensures must establish a matching function postcondition, got: {result:?}"
    );
}

// ── Direction (ii): NO over-rejection (legitimate calls work) ────────────────

#[test]
fn forward_unconditional_call_ensures_verifies() {
    // The legitimate forward case: call unconditionally, then assert the ensures.
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn good(a: u64) {
            let _ = mk(a);
            trust_vc::assert!(a == 7u64);
        }
    "#;
    let result = verify_with_context(code, "good");
    assert!(
        is_verified(&result),
        "a forward unconditional call then assert(ensures) must verify, got: {result:?}"
    );
}

#[test]
fn same_branch_forward_call_ensures_verifies() {
    let code = r#"
        #[trust_vc::ensures(x == 7u64)]
        fn mk(x: u64) -> u64 { 0u64 }

        fn good(c: bool, a: u64) {
            if c {
                let _ = mk(a);
                trust_vc::assert!(a == 7u64);
            }
        }
    "#;
    let result = verify_with_context(code, "good");
    assert!(
        is_verified(&result),
        "same-branch forward call+assert(ensures) must verify, got: {result:?}"
    );
}

#[test]
fn branch_guarded_valid_call_requires_implied_by_guard_verifies() {
    // Priority-2 over-rejection: need(c) has requires(c>10), called only under
    // `if c>100`, so the guard implies the precondition. Verus verifies this.
    let code = r#"
        #[trust_vc::requires(x > 10u64)]
        fn need(x: u64) -> u64 { 0u64 }

        fn g(c: u64) {
            if c > 100u64 {
                let _ = need(c);
            }
        }
    "#;
    let result = verify_with_context(code, "g");
    assert!(
        is_verified(&result),
        "a branch-guarded call whose requires is implied by the guard must verify, got: {result:?}"
    );
}

#[test]
fn unconditional_call_requires_unmet_is_counterexample() {
    // Control for the requires guard: an unconditional call whose precondition is
    // NOT established must still be rejected.
    let code = r#"
        #[trust_vc::requires(x > 10u64)]
        fn need(x: u64) -> u64 { 0u64 }

        fn g(c: u64) {
            let _ = need(c);
        }
    "#;
    let result = verify_with_context(code, "g");
    assert!(
        is_counterexample(&result),
        "an unconditional call with an unmet precondition must be a counterexample, got: {result:?}"
    );
}

#[test]
fn branch_guarded_call_requires_not_implied_is_counterexample() {
    // The guard does NOT imply the precondition (c>5 does not give c>10).
    let code = r#"
        #[trust_vc::requires(x > 10u64)]
        fn need(x: u64) -> u64 { 0u64 }

        fn g(c: u64) {
            if c > 5u64 {
                let _ = need(c);
            }
        }
    "#;
    let result = verify_with_context(code, "g");
    assert!(
        is_counterexample(&result),
        "a branch-guarded call whose requires is NOT implied by the guard must be rejected, got: {result:?}"
    );
}
