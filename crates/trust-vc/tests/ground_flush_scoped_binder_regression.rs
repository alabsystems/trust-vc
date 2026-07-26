// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guard for the ground-axiom-flush out-of-scope binder defect.
//!
//! A source-spec helper invoked inside `assert_forall_by` registers a ground
//! entry capturing the assert-forall-by universal binder (e.g. `i`). That binder
//! is only transiently in scope: it is declared while verifying its own
//! obligation and carried into a *later* obligation's setup as a proven fact.
//! Before the fix, `flush_ground_axioms_to_fixpoint` blindly re-encoded that
//! stale ground instance during the later obligation, whose scope no longer
//! declares `i`, producing an internal `VerifyResult::Error` ("flush ground
//! axioms ... undefined variable `i`") instead of a clean verdict.
//!
//! The fix drops ground instances that capture a binder no longer in scope. The
//! tests below assert (a) the verdicts are clean (never `Error`), (b) genuinely
//! true forall obligations still `Verified` (the in-scope body axiom is kept),
//! and (c) genuinely FALSE bodies are rejected — the fix never papers the
//! internal error over into a vacuous `Verified`.

use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked, VerifyResult,
};

fn verify(src: &str, case: &str) -> VerifyResult {
    let file = parse_file_allow_tracked(src).expect("scoped-binder regression source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist"));
    extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"))
        .verify()
}

fn assert_not_internal_error(case: &str, result: &VerifyResult) {
    assert!(
        !matches!(result, VerifyResult::Error { .. }),
        "{case} must not fail-stop with an internal error, got: {result:?}"
    );
}

/// Source-helper, shadowed binders, multiple obligations sharing the helper's
/// body axiom — the exact shape that crashed. Each forall holds (the helper is
/// `true`), so the only correct verdict is `Verified`.
const TRUE_SHAPE: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn helper_true(_i: int) -> bool { true }

#[trust_vc::ensures(true)]
fn shadowed_true(b: bool, _i: u64) {
    if b {
        let _i = 5;
        trust_vc::assert!(forall |i: int| helper_true(i) by {});
        trust_vc::assert!(forall |j: int| helper_true(j) by {});
    } else {
        let _i = 6;
        trust_vc::assert!(forall |i: int| helper_true(i) by {});
        trust_vc::assert!(forall |j: int| helper_true(j) by {});
    }
}
"#;

/// Same shape, but the helper body is FALSE: every forall is false. The fix must
/// produce a clean rejection (Counterexample / not-Verified), never a vacuous
/// pass and never an internal error.
const FALSE_SHAPE: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn helper_false(_i: int) -> bool { false }

#[trust_vc::ensures(true)]
fn shadowed_false(b: bool, _i: u64) {
    if b {
        let _i = 5;
        trust_vc::assert!(forall |i: int| helper_false(i) by {});
        trust_vc::assert!(forall |j: int| helper_false(j) by {});
    } else {
        let _i = 6;
        trust_vc::assert!(forall |i: int| helper_false(i) by {});
        trust_vc::assert!(forall |j: int| helper_false(j) by {});
    }
}
"#;

#[test]
fn shadowed_source_helper_true_forall_verifies_without_internal_error() {
    let result = verify(TRUE_SHAPE, "shadowed_true");
    assert_not_internal_error("shadowed_true", &result);
    assert!(
        matches!(result, VerifyResult::Verified),
        "all-true source-helper foralls should verify, got: {result:?}"
    );
}

#[test]
fn shadowed_source_helper_false_forall_is_rejected_not_vacuous() {
    let result = verify(FALSE_SHAPE, "shadowed_false");
    assert_not_internal_error("shadowed_false", &result);
    // The forall is genuinely false, so the fix must reject it. Crucially it must
    // NOT have been "fixed" by silently dropping the obligation into a vacuous
    // Verified.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "all-false source-helper foralls must be rejected with a counterexample, got: {result:?}"
    );
}
