// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The `&mut` CONTRACT VOCABULARY: `final(..)`, `mut_ref_future(..)`,
//! `mut_ref_current(..)`, and the refused `has_resolved(..)` / `after_borrow(..)`.
//!
//! # What was measured (2026-09-20), before any of this landed
//!
//! Four spellings the whole upstream `&mut` family is written in could not be
//! WRITTEN at all — not a proof-power gap, a vocabulary gap:
//!
//! * `final(x)` — verbatim: `Failed to parse target contract attribute …:
//!   expected an expression`. `final` is a RESERVED Rust keyword, so `syn`
//!   rejects it as a path segment and the whole clause dies.
//! * `mut_ref_future(x)` / `mut_ref_current(x)` / `has_resolved(x)` — verbatim:
//!   `type inference failed: unknown return type for function '<name>':
//!   register it in TypeEnv via prepare_context`.
//!
//! 202 of the 608 named upstream cases across `mut_refs*.rs` / `proph*.rs` use
//! at least one of the four.
//!
//! # The semantics, and why three of the four are SYNONYMS
//!
//! Verus's `&mut` model exposes exactly TWO endpoints of a parameter's borrow,
//! and every supported spelling names one of them (upstream
//! `mut_refs_temporaries.rs` pins the pairing with
//! `ensures mut_ref_future(a) == mut_ref_current(a) + 10`):
//!
//! | spelling                                         | endpoint |
//! |--------------------------------------------------|----------|
//! | `old(P)`, `*old(P)`, `mut_ref_current(P)`        | ENTRY    |
//! | bare `P` / `*P` in an `ensures`, `final(P)`, `*final(P)`, `mut_ref_future(P)` | FINAL |
//!
//! trust-vc ALREADY implements both endpoints soundly for a supported scalar
//! `&mut` parameter (`apply_mut_ref_final_state_to_postconditions` +
//! `capture_mut_ref_param_finals`). So `final(P)` is **not** a new value: it is
//! an exact synonym for what a bare `P` in an `ensures` already means, and it
//! routes through the SAME substitution seam, inheriting unchanged the
//! per-parameter validation (clean final, no escape, no early exit) and failing
//! closed on exactly the same shapes. Nothing here touches the prophecy
//! substrate (`mut_ref_prophecy.rs`), which stays DO NOT WIRE.
//!
//! # The bar these tests hold
//!
//! A vocabulary that parses and means the wrong thing is worse than one that
//! fails to parse: it turns a loud refusal into a silent wrong answer. So every
//! spelling is pinned in BOTH directions — a true claim about the endpoint
//! VERIFIES and its liar twin is REFUTED — and every position where the
//! endpoint is not soundly available is pinned as a NAMED refusal.

use super::*;
use crate::encoder::VerifyResult;
use crate::vc_extraction::extract_verification_conditions_with_file_context;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let item = find_function(&file, func).unwrap();
    extract_verification_conditions(item)
        .unwrap_or_else(|err| panic!("{func} should extract: {err}"))
        .verify()
}

fn refusal(code: &str, func: &str) -> String {
    let file = parse_file(code).unwrap();
    let item = find_function(&file, func).unwrap();
    match extract_verification_conditions(item) {
        Err(err) => err.to_string(),
        Ok(vc) => match vc.verify() {
            VerifyResult::Error { message, .. } => message,
            other => panic!("{func} must be refused, got: {other:?}"),
        },
    }
}

fn assert_verified(code: &str, func: &str) {
    assert_eq!(
        verdict(code, func),
        VerifyResult::Verified,
        "a TRUE endpoint claim must verify"
    );
}

fn assert_refuted(code: &str, func: &str) {
    assert!(
        matches!(verdict(code, func), VerifyResult::Counterexample { .. }),
        "the liar twin must be REFUTED, never verified"
    );
}

// --- `final(P)` / `*final(P)` ------------------------------------------------

/// `*final(x)` after `*x = 5` names 5. Both directions.
#[test]
fn final_deref_names_the_post_body_value() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(*final(x) == 5u64)]
        fn t(x: &mut u64) { *x = 5u64; }

        #[requires(x == 0u64)]
        #[ensures(*final(x) == 0u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

/// Verus's `final_` returns `&mut T`, so the upstream spelling is `*final(x)`.
/// trust-vc has no reference terms at all — a `&mut` scalar parameter IS its
/// value — so the bare `final(x)` denotes that same value, exactly as bare `x`
/// already does in an `ensures`. Both directions.
#[test]
fn final_without_deref_is_the_same_value() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(final(x) == 5u64)]
        fn t(x: &mut u64) { *x = 5u64; }

        #[requires(x == 0u64)]
        #[ensures(final(x) == 0u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

/// `final(x)` is a SYNONYM of bare `x` in an `ensures` — the same obligation,
/// not a second mechanism. Pinned by agreement on the same body in both
/// directions rather than by asserting on internal state.
#[test]
fn final_agrees_with_the_bare_spelling_on_the_same_body() {
    let code = r#"
        #[requires(x == 3u64)]
        #[ensures(x == 4u64)]
        fn bare_t(x: &mut u64) { *x = *x + 1u64; }

        #[requires(x == 3u64)]
        #[ensures(*final(x) == 4u64)]
        fn final_t(x: &mut u64) { *x = *x + 1u64; }

        #[requires(x == 3u64)]
        #[ensures(x == 3u64)]
        fn bare_f(x: &mut u64) { *x = *x + 1u64; }

        #[requires(x == 3u64)]
        #[ensures(*final(x) == 3u64)]
        fn final_f(x: &mut u64) { *x = *x + 1u64; }
    "#;
    assert_verified(code, "bare_t");
    assert_verified(code, "final_t");
    assert_refuted(code, "bare_f");
    assert_refuted(code, "final_f");
}

// --- `mut_ref_future(P)` -----------------------------------------------------

/// `mut_ref_future(x)` is the same FINAL endpoint as `*final(x)`.
#[test]
fn mut_ref_future_names_the_post_body_value() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(mut_ref_future(x) == 5u64)]
        fn t(x: &mut u64) { *x = 5u64; }

        #[requires(x == 0u64)]
        #[ensures(mut_ref_future(x) == 0u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

// --- `mut_ref_current(P)` ----------------------------------------------------

/// `mut_ref_current(x)` in an `ensures` is the ENTRY value — the endpoint the
/// borrow started at, NOT the current-at-exit state. The liar twin claims the
/// post-body value and must be refuted; if `mut_ref_current` had silently been
/// wired to the final value, the twin would VERIFY.
#[test]
fn mut_ref_current_in_ensures_is_the_entry_value() {
    let code = r#"
        #[requires(x == 3u64)]
        #[ensures(mut_ref_current(x) == 3u64)]
        fn t(x: &mut u64) { *x = 5u64; }

        #[requires(x == 3u64)]
        #[ensures(mut_ref_current(x) == 5u64)]
        fn f(x: &mut u64) { *x = 5u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

/// The upstream `mut_refs_temporaries.rs` shape, verbatim in trust-vc surface:
/// `requires mut_ref_current(a) < 100`, `ensures mut_ref_future(a) ==
/// mut_ref_current(a) + 10`. Both endpoints in one contract, both directions.
#[test]
fn both_endpoints_in_one_contract() {
    let code = r#"
        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(mut_ref_future(x) == mut_ref_current(x) + 2u64)]
        fn t(x: &mut u64) { *x = *x + 2u64; }

        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(mut_ref_future(x) == mut_ref_current(x) + 3u64)]
        fn f(x: &mut u64) { *x = *x + 2u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

/// `mut_ref_current` is legal in a `requires`, where bare `*x` already means the
/// entry value, and the contract still resolves to the entry endpoint in both
/// directions.
#[test]
fn mut_ref_current_in_requires_reads_entry_state() {
    let code = r#"
        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(*final(x) == 4u64)]
        fn req_t(x: &mut u64) { *x = *x + 2u64; }

        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(*final(x) == 5u64)]
        fn req_f(x: &mut u64) { *x = *x + 2u64; }
    "#;
    assert_verified(code, "req_t");
    assert_refuted(code, "req_f");
}

// --- the shapes the task named -----------------------------------------------

/// A `&mut` parameter that is NEVER written: entry == final on every path, so
/// the FINAL endpoint is the entry value. Both directions — and the liar twin is
/// what stops the no-clean-final fallback from being a hole.
#[test]
fn never_written_parameter_has_entry_as_its_final_value() {
    let code = r#"
        #[requires(x == 7u64)]
        #[ensures(*final(x) == 7u64)]
        fn t(x: &mut u64) { let _ = *x; }

        #[requires(x == 7u64)]
        #[ensures(*final(x) == 8u64)]
        fn f(x: &mut u64) { let _ = *x; }

        #[requires(x == 7u64)]
        #[ensures(mut_ref_future(x) == 7u64)]
        fn t2(x: &mut u64) { let _ = *x; }

        #[requires(x == 7u64)]
        #[ensures(mut_ref_future(x) == 8u64)]
        fn f2(x: &mut u64) { let _ = *x; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
    assert_verified(code, "t2");
    assert_refuted(code, "f2");
}

/// Written on ONE branch only: the final value is havoced by the join, so
/// `final(x)` fails CLOSED — exactly as bare `x` does. BOTH the true and the
/// false claim are refused; a spelling that verified the "true" one here would
/// be proving the write on a path where it did not happen.
#[test]
fn one_branch_write_fails_closed_in_both_directions() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(*final(x) == 5u64)]
        fn a(x: &mut u64, b: bool) { if b { *x = 5u64; } }

        #[requires(x == 0u64)]
        #[ensures(*final(x) == 0u64)]
        fn c(x: &mut u64, b: bool) { if b { *x = 5u64; } }
    "#;
    for func in ["a", "c"] {
        let message = refusal(code, func);
        assert!(
            message.contains("havoced by a branch/loop join"),
            "{func}: expected the branch-join refusal, got: {message}"
        );
        assert!(
            !message.contains("__trust_vc_mut_ref_final"),
            "{func}: the parse-time marker must never reach a diagnostic: {message}"
        );
    }
}

/// A loop that may run zero times never lets `final(x)` claim the loop body's
/// write. Fails closed.
#[test]
fn zero_trip_loop_write_fails_closed() {
    let code = r#"
        #[requires(x == 0u64)]
        #[ensures(*final(x) == 3u64)]
        fn f(x: &mut u64, n: u64) {
            let mut i: u64 = 0u64;
            while i < n { *x = 3u64; i = i + 1u64; }
        }
    "#;
    let _ = refusal(code, "f");
}

/// The reference ESCAPES (passed to a call), so the referent may be mutated
/// outside the tracked value. `final(x)` must fail closed rather than claim the
/// entry value survived.
#[test]
fn escaping_reference_fails_closed() {
    let code = r#"
        #[ensures(true)]
        fn bump(v: &mut u64) { *v = 99u64; }

        #[requires(x == 7u64)]
        #[ensures(*final(x) == 7u64)]
        fn f(x: &mut u64) { bump(x); }
    "#;
    let message = refusal(code, "f");
    assert!(
        message.contains("escapes the body"),
        "expected the escape refusal, got: {message}"
    );
}

/// Two `&mut` parameters, relationally. Rust's borrow checker makes two `&mut`
/// parameters of a safe function non-aliasing, so the hazard is not that they
/// COULD name one place but that each must resolve to its OWN final value.
#[test]
fn two_mut_ref_parameters_resolve_independently() {
    let code = r#"
        #[ensures(*final(a) == *final(b))]
        fn t(a: &mut u64, b: &mut u64) { *a = 9u64; *b = 9u64; }

        #[ensures(*final(a) == *final(b))]
        fn f(a: &mut u64, b: &mut u64) { *a = 9u64; *b = 8u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

/// `final` mixed with `old` in ONE clause: the two endpoints must stay distinct
/// (a resolver that substituted into its own replacement would collapse them).
#[test]
fn final_and_old_in_one_clause_stay_distinct() {
    let code = r#"
        #[requires(x == 1u64)]
        #[ensures(*final(x) == *old(x) + 1u64)]
        fn t(x: &mut u64) { *x = *x + 1u64; }

        #[requires(x == 1u64)]
        #[ensures(*final(x) == *old(x) + 2u64)]
        fn f(x: &mut u64) { *x = *x + 1u64; }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

// --- NAMED refusals ----------------------------------------------------------

/// `final()` over a parameter that is not a `&mut` reference is a HARD error.
/// A by-value parameter keeps ENTRY-value postcondition semantics, so accepting
/// `final(y)` there would read the entry value under a name that promises the
/// exit value — a silent wrong answer.
#[test]
fn final_over_a_non_mut_ref_parameter_is_refused_by_name() {
    let code = r#"
        #[ensures(*final(y) == 4u64)]
        fn f(x: &mut u64, y: u64) { *x = y; }
    "#;
    let message = refusal(code, "f");
    assert!(
        message.contains("final() is only supported on scalar &mut parameters"),
        "got: {message}"
    );
}

/// The FINAL endpoint in a `requires` names a value that does not exist at
/// entry. Refused BY NAME for both spellings — never silently resolved to the
/// entry symbol, which is the reading that would make
/// `#[requires(*final(x) == 5)]` a tautology for a body that writes 5.
#[test]
fn final_endpoint_in_a_requires_is_refused_by_name() {
    for (spelling, code) in [
        (
            "final",
            r#"
            #[requires(*final(x) == 5u64)]
            #[ensures(true)]
            fn f(x: &mut u64) { *x = 5u64; }
        "#,
        ),
        (
            "mut_ref_future",
            r#"
            #[requires(mut_ref_future(x) == 5u64)]
            #[ensures(true)]
            fn f(x: &mut u64) { *x = 5u64; }
        "#,
        ),
    ] {
        let message = refusal(code, "f");
        assert!(
            message.contains("at function EXIT and is only supported in an `ensures`"),
            "{spelling}: got: {message}"
        );
        assert!(message.contains(spelling), "{spelling}: got: {message}");
    }
}

/// Nested `final(final(x))` (and its deref spellings) is refused: the argument
/// must be a bare parameter. Verus's `final_` takes a `&mut T`, and this engine
/// has no reference term to feed back in, so nesting has no meaning here.
#[test]
fn nested_final_is_refused_by_name() {
    for code in [
        r#"
            #[ensures(*final(*final(x)) == 5u64)]
            fn f(x: &mut u64) { *x = 5u64; }
        "#,
        r#"
            #[ensures(final(final(x)) == 5u64)]
            fn f(x: &mut u64) { *x = 5u64; }
        "#,
    ] {
        let message = refusal(code, "f");
        assert!(
            message.contains("the argument must be a bare parameter"),
            "got: {message}"
        );
        assert!(
            !message.contains("__trust_vc_mut_ref_final"),
            "the parse-time marker must never reach a diagnostic: {message}"
        );
    }
}

/// `final()` in a BODY assertion names the end of a borrow mid-function — the
/// prophecy value this engine does not track. Refused by name, and the refusal
/// must not leak the parse-time marker.
#[test]
fn final_in_a_body_assertion_is_refused_by_name() {
    let code = r#"
        #[ensures(true)]
        fn f(x: &mut u64) { *x = 5u64; assert!(*final(x) == 5u64); }
    "#;
    let message = refusal(code, "f");
    assert!(
        message.contains("names the value of a `&mut` place at the END of its borrow"),
        "got: {message}"
    );
    assert!(
        !message.contains("__trust_vc_mut_ref_final"),
        "the parse-time marker must never reach a diagnostic: {message}"
    );
}

/// `has_resolved()` is REFUSED, not approximated.
///
/// It is a predicate over a mutable REFERENCE (Verus axiomatizes
/// `has_resolved(t) ==> mut_ref_current(t) == mut_ref_future(t)`), and this
/// engine models a `&mut` parameter only by the scalar VALUE behind it.
/// Lowering `has_resolved(a)` onto that value would identify two distinct
/// references whose values coincide, so a resolution fact assumed for one would
/// transfer to the other — a false `Verified`. The second case below is exactly
/// that transfer; it must never verify.
#[test]
fn has_resolved_is_refused_by_name() {
    let code = r#"
        #[ensures(true)]
        fn f(x: &mut u64) { *x = 5u64; assert!(has_resolved(x)); }

        #[requires(has_resolved(a))]
        #[ensures(has_resolved(b))]
        fn transfer(a: &mut u64, b: &mut u64) { *a = 5u64; *b = 5u64; }
    "#;
    for func in ["f", "transfer"] {
        let message = refusal(code, func);
        assert!(
            message.contains("`has_resolved()` is refused"),
            "{func}: got: {message}"
        );
    }
}

/// `after_borrow()` names a place's value after a LOCAL borrow of it ends. This
/// engine tracks borrow endpoints only for `&mut` PARAMETERS, so it is refused
/// by name rather than approximated.
#[test]
fn after_borrow_is_refused_by_name() {
    let code = r#"
        #[ensures(true)]
        fn f(x: &mut u64) { *x = 5u64; assert!(after_borrow(x) == 5u64); }
    "#;
    let message = refusal(code, "f");
    assert!(
        message.contains("`after_borrow()` is refused"),
        "got: {message}"
    );
}

// --- the one place the two readings genuinely differ -------------------------

/// THE DISCRIMINATOR, and the reason this file exists.
///
/// `mut_ref_current(P)` does NOT mean one thing everywhere:
///
/// * at the CONTRACT boundary the parameter denotes the reference AS PASSED IN,
///   so it is the ENTRY value — upstream `mut_refs_temporaries.rs` proves
///   `ensures mut_ref_future(a) == mut_ref_current(a) + 10` for a body that does
///   `*a = *a + 10`, which is only provable under the entry reading;
/// * in a BODY it is the value behind the place AT THAT PROGRAM POINT — upstream
///   `mut_refs.rs::test_array` requires `mut_ref_current(j)[0] == X{a:0,b:1}`,
///   mutates `j[0]`, and then PROVES `assert(mut_ref_current(j)[0] ==
///   X{a:0,b:0})`.
///
/// An implementation that picked either reading for both positions would be
/// silently wrong in the other. `body_liar` is the catastrophic direction: a
/// post-write assertion checked against pre-state. It must be REFUTED.
#[test]
fn mut_ref_current_is_entry_in_a_contract_and_current_in_a_body() {
    let code = r#"
        #[requires(x == 3u64)]
        #[ensures(true)]
        fn body_t(x: &mut u64) { *x = 5u64; assert!(mut_ref_current(x) == 5u64); }

        #[requires(x == 3u64)]
        #[ensures(true)]
        fn body_liar(x: &mut u64) { *x = 5u64; assert!(mut_ref_current(x) == 3u64); }

        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(mut_ref_future(x) == mut_ref_current(x) + 2u64)]
        fn contract_t(x: &mut u64) { *x = *x + 2u64; }

        #[requires(mut_ref_current(x) == 2u64)]
        #[ensures(mut_ref_future(x) == mut_ref_current(x))]
        fn contract_liar(x: &mut u64) { *x = *x + 2u64; }
    "#;
    assert_verified(code, "body_t");
    assert_refuted(code, "body_liar");
    assert_verified(code, "contract_t");
    assert_refuted(code, "contract_liar");
}

/// The body reading also holds for a LOCAL `&mut` borrow, where there is no
/// parameter entry symbol to confuse it with. Both directions.
#[test]
fn mut_ref_current_on_a_local_borrow_reads_the_current_value() {
    let code = r#"
        #[ensures(true)]
        fn t() {
            let mut value: u64 = 20u64;
            let value_ref: &mut u64 = &mut value;
            *value_ref = 30u64;
            assert!(mut_ref_current(value_ref) == 30u64);
        }

        #[ensures(true)]
        fn f() {
            let mut value: u64 = 20u64;
            let value_ref: &mut u64 = &mut value;
            *value_ref = 30u64;
            assert!(mut_ref_current(value_ref) == 20u64);
        }
    "#;
    assert_verified(code, "t");
    assert_refuted(code, "f");
}

// --- the parse-time marker must never reach a diagnostic -------------------
//
// The branch-join refusal scrubs `__trust_vc_mut_ref_final` back to the source
// spelling (`one_branch_write_fails_closed_in_both_directions` pins it). THREE
// sibling refusals used to render the same contract string RAW, so a
// `final(..)` clause on a non-scalar `&mut` parameter answered with a symbol
// that does not exist in the author's source:
//
//   Postcondition `* __trust_vc_mut_ref_final (a) == (5u64 , 6u64)` reads …
//   Postcondition `* __trust_vc_mut_ref_final (s) == * old (s)` reads …
//   Postcondition `__trust_vc_mut_ref_final (v) . len () == 1int` reads …
//
// These are fail-closed refusals either way — no verdict moved — but a refusal
// that names a private marker sends the author hunting for a spelling they
// never wrote. Each is now scrubbed, and each is pinned here in BOTH
// directions: the marker is absent AND the source spelling `final` is present.

/// `&mut (u64, u64)` — a direct field write on a non-scalar `&mut` parameter
/// (`mut_ref_place_mutation_two_state_error`).
#[test]
fn place_mutation_refusal_shows_the_source_spelling_not_the_marker() {
    let code = r#"
        #[ensures(*final(a) == (5u64, 6u64))]
        fn f(a: &mut (u64, u64)) { a.0 = 5u64; a.1 = 6u64; }
    "#;
    let message = refusal(code, "f");
    assert!(
        !message.contains("__trust_vc_mut_ref_final"),
        "the parse-time marker must never reach a diagnostic: {message}"
    );
    assert!(
        message.contains("final (a)"),
        "the refusal must echo the SOURCE spelling: {message}"
    );
}

/// `&mut S` mutated by a `&mut self` method call
/// (`mut_ref_struct_two_state_error`).
#[test]
fn struct_method_mutation_refusal_shows_the_source_spelling_not_the_marker() {
    let code = r#"
        struct S { f: u64 }

        impl S {
            #[ensures(true)]
            fn bump(&mut self) { self.f = self.f + 1u64; }
        }

        #[ensures(*final(s) == *old(s))]
        fn f(s: &mut S) { s.bump(); }
    "#;
    // The struct route needs the `impl` block in scope, so this one extracts
    // WITH file context (the bare-item helper would refuse earlier, on
    // position, and never reach the struct builder).
    let file = parse_file(code).unwrap();
    let item = find_function(&file, "f").unwrap();
    let message = match extract_verification_conditions_with_file_context(&file, item) {
        Err(err) => err.to_string(),
        Ok(vc) => match vc.verify() {
            VerifyResult::Error { message, .. } => message,
            other => panic!("f must be refused, got: {other:?}"),
        },
    };
    assert!(
        message.contains("reads `&mut` struct/enum parameter"),
        "expected the struct-method-mutation refusal, got: {message}"
    );
    assert!(
        !message.contains("__trust_vc_mut_ref_final"),
        "the parse-time marker must never reach a diagnostic: {message}"
    );
    assert!(
        message.contains("final (s)"),
        "the refusal must echo the SOURCE spelling: {message}"
    );
}

/// `&mut Vec<u64>` mutated by `push` (`mut_ref_collection_two_state_error`).
#[test]
fn collection_method_mutation_refusal_shows_the_source_spelling_not_the_marker() {
    let code = r#"
        #[ensures(final(v).len() == 1int)]
        fn f(v: &mut Vec<u64>) { v.push(1u64); }
    "#;
    let message = refusal(code, "f");
    assert!(
        !message.contains("__trust_vc_mut_ref_final"),
        "the parse-time marker must never reach a diagnostic: {message}"
    );
    assert!(
        message.contains("final (v)"),
        "the refusal must echo the SOURCE spelling: {message}"
    );
}
