// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Two-state semantics for scalar `&mut` parameters in postconditions.
//!
//! A *bare* `&mut` scalar parameter `P` (or `*P`) in a postcondition denotes its
//! FINAL (post-body) value, matching Verus and `design-new-mut-ref.md`. The
//! catastrophic bug these tests pin: the string body model used to resolve `P`
//! to the ENTRY snapshot, so a postcondition a body mutation falsifies would
//! wrongly `Verified`. The non-negotiable invariant is that **no false `&mut`
//! postcondition ever verifies** — false ones are `Counterexample`, and shapes
//! whose final value cannot be soundly resolved fail closed (`Err`).

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let item = find_function(&file, func).unwrap();
    extract_verification_conditions(item)
        .unwrap_or_else(|err| panic!("{func} should extract: {err}"))
        .verify()
}

fn extraction_fails_closed(code: &str, func: &str) {
    let file = parse_file(code).unwrap();
    let item = find_function(&file, func).unwrap();
    match extract_verification_conditions(item) {
        Err(_) => {}
        Ok(vc) => match vc.verify() {
            VerifyResult::Error { .. } => {}
            other => panic!("{func} should fail closed (Err/Error), got: {other:?}"),
        },
    }
}

/// THE catastrophic case: `ensures(x == 0)` after `*x = 5` must NOT verify.
/// Before the fix this returned `Verified` (false) because `x` read the entry
/// snapshot; now `x` denotes the final value `5`, so `5 == 0` is refuted.
#[test]
fn false_mut_ref_postcondition_after_write_is_counterexample() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 0u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert!(
        matches!(verdict(code, "f"), VerifyResult::Counterexample { .. }),
        "a FALSE &mut postcondition must never verify"
    );
}

/// The true postcondition `ensures(x == 5)` after `*x = 5` verifies (proper
/// final-state fix, not merely fail-closed).
#[test]
fn true_mut_ref_postcondition_after_write_verifies() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 5u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_eq!(verdict(code, "f"), VerifyResult::Verified);
}

/// A different false value `ensures(x == 1)` after `*x = 5` is refuted.
#[test]
fn other_false_mut_ref_postcondition_is_counterexample() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 1u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert!(matches!(
        verdict(code, "f"),
        VerifyResult::Counterexample { .. }
    ));
}

/// The explicit-deref spelling `*x` in a postcondition resolves to the final
/// value too — true verifies, false refutes.
#[test]
fn deref_spelling_resolves_to_final_value() {
    let true_code = r#"
        #[requires(x == 0u64)]
        #[ensures(*x == 5u64)]
        fn t(x: &mut u64) { *x = 5u64; }
    "#;
    let false_code = r#"
        #[requires(x == 0u64)]
        #[ensures(*x == 0u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_eq!(verdict(true_code, "t"), VerifyResult::Verified);
    assert!(matches!(
        verdict(false_code, "f"),
        VerifyResult::Counterexample { .. }
    ));
}

/// An arithmetic mutation `*x = *x + 1` resolves the postcondition against the
/// final value `entry + 1` (the `*x` inside the final value keeps its entry
/// meaning), so `ensures(x == 4)` verifies from `requires(x == 3)` and
/// `ensures(x == 3)` is refuted.
#[test]
fn arithmetic_mutation_final_value() {
    let true_code = r#"
        #[requires(x == 3u64)]
        #[ensures(x == 4u64)]
        fn t(x: &mut u64) { *x = *x + 1u64; }
    "#;
    let false_code = r#"
        #[requires(x == 3u64)]
        #[ensures(x == 3u64)]
        fn f(x: &mut u64) { *x = *x + 1u64; }
    "#;
    assert_eq!(verdict(true_code, "t"), VerifyResult::Verified);
    assert!(matches!(
        verdict(false_code, "f"),
        VerifyResult::Counterexample { .. }
    ));
}

/// A relational postcondition over two `&mut` params resolves each to its own
/// final value: `ensures(a == b)` verifies when both are written `9`, and is
/// refuted when they diverge.
#[test]
fn relational_two_mut_ref_params() {
    let true_code = r#"
        #[ensures(a == b)]
        fn t(a: &mut u64, b: &mut u64) { *a = 9u64; *b = 9u64; }
    "#;
    let false_code = r#"
        #[ensures(a == b)]
        fn f(a: &mut u64, b: &mut u64) { *a = 9u64; *b = 8u64; }
    "#;
    assert_eq!(verdict(true_code, "t"), VerifyResult::Verified);
    assert!(matches!(
        verdict(false_code, "f"),
        VerifyResult::Counterexample { .. }
    ));
}

/// No over-correction: a `&mut` param that is never mutated keeps entry == final,
/// so `ensures(x == entry)` still verifies.
#[test]
fn unmutated_mut_ref_postcondition_uses_entry_value() {
    let code = r#"
        #[requires(x == 7u64)]
        #[ensures(x == 7u64)]
        fn f(x: &mut u64) {}
    "#;
    assert_eq!(verdict(code, "f"), VerifyResult::Verified);
}

/// `bool` scalar `&mut` params go through the same path.
#[test]
fn bool_mut_ref_final_value() {
    let true_code = r#"
        #[requires(x == false)]
        #[ensures(x == true)]
        fn t(x: &mut bool) { *x = true; }
    "#;
    let false_code = r#"
        #[requires(x == false)]
        #[ensures(x == false)]
        fn f(x: &mut bool) { *x = true; }
    "#;
    assert_eq!(verdict(true_code, "t"), VerifyResult::Verified);
    assert!(matches!(
        verdict(false_code, "f"),
        VerifyResult::Counterexample { .. }
    ));
}

/// Body-level `assert!(*x == 5)` after `*x = 5` already tracked the current
/// value correctly; the fix leaves that behavior unchanged.
#[test]
fn body_assert_current_value_unchanged() {
    let code = r#"
        #[requires(x == 0u64)]
        fn f(x: &mut u64) {
            *x = 5u64;
            assert!(*x == 5u64);
        }
    "#;
    assert_eq!(verdict(code, "f"), VerifyResult::Verified);
}

/// A mutation in only one branch havocs the final value (the conditional write
/// is not cleanly tracked to the exit): the postcondition fails closed rather
/// than risk a false `Verified` on the unwritten path.
#[test]
fn branch_havoced_mut_ref_postcondition_fails_closed() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 0u64)]
        fn f(x: &mut u64, c: bool) { if c { *x = 5u64; } }
    "#;
    extraction_fails_closed(code, "f");
}

/// An early `return` means the fall-through final value need not hold on the
/// early-exit path (where `*x == 1`), so the postcondition fails closed.
#[test]
fn early_return_mut_ref_postcondition_fails_closed() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 5u64)]
        fn f(x: &mut u64, c: bool) {
            if c { *x = 1u64; return; }
            *x = 5u64;
        }
    "#;
    extraction_fails_closed(code, "f");
}

/// Passing the `&mut` reference to a call may mutate the referent outside the
/// caller's value-numbering, so a postcondition over the escaped param fails
/// closed even though the tracked value happens to be `5`.
#[test]
fn escaping_mut_ref_postcondition_fails_closed() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(x == 5u64)]
        fn f(x: &mut u64) {
            *x = 5u64;
            helper(x);
        }
        fn helper(_x: &mut u64) {}
    "#;
    extraction_fails_closed(code, "f");
}

/// By-value `mut x: u64` keeps its (Verus-faithful) ENTRY-value postcondition
/// semantics: `result == x` with `result = z = entry x` and `x = 5` verifies,
/// proving the fix does NOT touch non-reference mutable parameters.
#[test]
fn by_value_mut_param_keeps_entry_semantics() {
    let code = r#"
        #[ensures(result == x)]
        fn f(mut x: u64) -> u64 {
            let z = x;
            x = 5u64;
            let _ = x;
            z
        }
    "#;
    assert_eq!(verdict(code, "f"), VerifyResult::Verified);
}

// ── classic `old()` in contracts (slice A) — string-level resolver units ────
//
// `old(P)` / `*old(P)` denotes the ENTRY value of a scalar `&mut` param and is
// rewritten to the bare entry symbol `P`; bare `P` / `*P` keeps FINAL-value
// substitution. The rewriter must never recurse into a replacement: the final
// value string is expressed over ENTRY symbols, and the `P` inserted for
// `old(P)` IS an entry symbol — re-substituting either would silently flip
// entry references into post-state values (the directionality landmine).

fn resolver_params(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(ToString::to_string).collect()
}

fn resolver_finals(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
    pairs
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
        .collect()
}

/// T5 (double-substitution guard, string level): with final `x + 1u64`, the
/// bare `x` substitutes to the final while `old(x)` resolves to the bare entry
/// symbol — and NEITHER replacement is re-substituted (a recursing rewriter
/// would produce `x + 1u64 == x + 1u64 + 1u64` or worse).
#[test]
fn old_rewrite_is_entry_symbol_and_never_resubstituted() {
    let outcome = rewrite_mut_ref_postcondition(
        "x == old(x) + 1u64",
        &resolver_params(&["x"]),
        &resolver_finals(&[("x", "x + 1u64")]),
    )
    .expect("old(x) over a scalar &mut param must rewrite");
    assert_eq!(outcome.rewritten, "x + 1u64 == x + 1u64");
    assert_eq!(outcome.referenced_params, resolver_params(&["x"]));
    assert_eq!(outcome.old_referenced_params, resolver_params(&["x"]));
    assert!(!outcome.closure_mentions_param);
}

/// An old-only condition records the param ONLY in `old_referenced_params`
/// (the caller's clean-final/no-escape/no-early-exit validation must not run
/// for it), and the rewritten string is the bare entry symbol.
#[test]
fn old_only_reference_bypasses_final_value_bookkeeping() {
    let outcome = rewrite_mut_ref_postcondition(
        "old(x) < 100u64",
        &resolver_params(&["x"]),
        &resolver_finals(&[("x", "5u64")]),
    )
    .expect("old-only condition must rewrite");
    assert_eq!(outcome.rewritten, "x < 100u64");
    assert!(outcome.referenced_params.is_empty());
    assert_eq!(outcome.old_referenced_params, resolver_params(&["x"]));
}

/// The outer-deref spelling `*old(x)` (and the inner-deref argument `old(*x)`)
/// resolve exactly like `old(x)`: the WHOLE form — including the deref —
/// becomes the bare entry symbol, so no unsupported deref survives to the
/// encoder.
#[test]
fn deref_old_spellings_resolve_to_bare_entry_symbol() {
    for condition in ["*old(x) == 5u64", "old(*x) == 5u64", "*old(*x) == 5u64"] {
        let outcome = rewrite_mut_ref_postcondition(
            condition,
            &resolver_params(&["x"]),
            &resolver_finals(&[("x", "7u64")]),
        )
        .unwrap_or_else(|err| panic!("`{condition}` must rewrite: {err}"));
        assert_eq!(outcome.rewritten, "x == 5u64", "for `{condition}`");
        assert_eq!(outcome.old_referenced_params, resolver_params(&["x"]));
    }
}

/// `old()` over anything that is not a supported scalar `&mut` parameter is a
/// HARD error — silently treating `old(y)` as the current value would
/// over-prove.
#[test]
fn old_over_non_mut_ref_param_is_hard_error() {
    let err = match rewrite_mut_ref_postcondition(
        "old(y) == 1u64",
        &resolver_params(&["x"]),
        &resolver_finals(&[]),
    ) {
        Err(err) => err,
        Ok(outcome) => panic!(
            "old(y) with y not a scalar &mut param must fail closed, got `{}`",
            outcome.rewritten
        ),
    };
    assert!(
        err.to_string()
            .contains("old() is only supported on scalar &mut parameters"),
        "got: {err}"
    );
}

/// `old(..)` with a non-bare argument (arithmetic, fields, wrong arity) is a
/// HARD error — only `old(P)` / `*old(P)` are in slice A's sound scope.
#[test]
fn old_with_non_bare_argument_is_hard_error() {
    for condition in [
        "old(x + 1u64) == 6u64",
        "old(s.f) == 6u64",
        "old(x, x) == 6u64",
        "old() == 6u64",
    ] {
        match rewrite_mut_ref_postcondition(
            condition,
            &resolver_params(&["x"]),
            &resolver_finals(&[]),
        ) {
            Err(err) => assert!(
                err.to_string()
                    .contains("old() is only supported on scalar &mut parameters"),
                "for `{condition}`, got: {err}"
            ),
            Ok(outcome) => panic!(
                "`{condition}` must fail closed, got rewritten `{}`",
                outcome.rewritten
            ),
        }
    }
}
