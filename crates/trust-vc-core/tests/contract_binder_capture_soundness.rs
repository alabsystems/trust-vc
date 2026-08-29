// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! CARDINAL FALSE VERIFY (family `scopes`): the call-site contract substituter
//! is keyed by BARE PARAMETER NAME and had no binder awareness, so it also
//! rewrote occurrences that a `forall`/`exists`/closure binder INSIDE the clause
//! had re-bound.
//!
//! A callee `#[requires(forall|m: int| m <= 100)] fn callee(m: u64)` therefore
//! presented its caller with `forall|m: int| 5 <= 100` — a tautology — instead
//! of the unsatisfiable real clause. Since no call site can discharge
//! `forall|m: int| m <= 100`, the callee's own body verified only vacuously
//! ("assumptions are contradictory") and its `ensures(result == 1)` was a lie
//! about a body returning `0`; the caller nevertheless showed a green
//! `verified` while asserting `r == 1`.
//!
//! The fix keys substitution by SCOPE, not by bare name: bound occurrences are
//! skipped, free ones are always substituted. BOTH halves are load-bearing —
//! skipping a free occurrence would let it re-bind to a same-named local in the
//! CALLER's scope, which is the same defect pointing the other way. Every
//! narrowness pin below exists to hold one of those two halves down.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/contract_binder_capture_soundness.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[track_caller]
fn must_refute(name: &str, why: &str) {
    let v = verify_function_from_file(&fx(), name);
    eprintln!("[binder-capture] {name} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {name} must not verify ({why}); got {v:?}"
    );
}

#[track_caller]
fn must_verify(name: &str, why: &str) {
    let v = verify_function_from_file(&fx(), name);
    eprintln!("[binder-capture] {name} => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "OVER-REJECTION: {name} must still verify ({why}); got {v:?}"
    );
}

// ------------------------- the confirmed false verify ----------------------

#[test]
fn requires_binder_capture_literal_arg_must_refute() {
    must_refute(
        "capture_literal_arg_must_refute",
        "`forall|m: int| m <= 100` is false, so the call is illegal, and the \
         asserted `r == 1` is false of a body returning 0",
    );
}

#[test]
fn requires_binder_capture_local_arg_must_refute() {
    must_refute(
        "capture_local_arg_must_refute",
        "same clause reached through a local rather than a literal argument",
    );
}

/// THE DISCRIMINATOR. An unprovable CLOSED clause cannot change verdict with the
/// argument value; before the fix `5` verified while `200` was refuted. If this
/// pair ever splits again, the binder is being captured.
#[test]
fn requires_verdict_must_not_depend_on_the_argument_value() {
    must_refute(
        "arg_value_small_must_refute",
        "the clause is closed and false — the argument cannot make it provable",
    );
    must_refute(
        "arg_value_big_must_refute",
        "the clause is closed and false — the argument cannot make it provable",
    );
}

/// CONTROL: the identical clause with the binder renamed so it shadows nothing.
/// Always refuted, before and after — it pins that the cases above turn on the
/// shadowing and not on anything else in the shape.
#[test]
fn control_without_shadowing_binder_must_refute() {
    must_refute(
        "control_no_shadow_must_refute",
        "control: renamed binder, same unprovable clause",
    );
}

/// One clause holding a FREE and a BOUND occurrence of the same name. Handling
/// either one wrongly makes the clause provable.
#[test]
fn free_and_bound_occurrence_in_one_clause_must_refute() {
    must_refute(
        "mixed_free_and_bound_must_refute",
        "`m > 0 && forall|m: int| m <= 100` must substitute only the free `m`",
    );
}

/// The `ensures` side: capture there falsifies an ASSUMPTION, which makes every
/// later obligation vacuous rather than unprovable.
#[test]
fn ensures_binder_capture_must_refute() {
    must_refute(
        "ensures_binder_capture_must_refute",
        "`exists|a: int| a > 0` must not collapse to `exists|a: int| 0 > 0`",
    );
}

// ------------------------------ narrowness pins ----------------------------
// A fix that declines whenever a binder shadows a parameter would pass every
// test above and be a pure capability loss. These hold the other edge.

#[test]
fn shadowing_binder_over_a_true_clause_must_still_verify() {
    must_verify(
        "shadowed_binder_tautology_must_verify",
        "`forall|m: int| m <= 100 || m > 100` is a tautology; the call is legal",
    );
}

#[test]
fn substitution_under_a_non_colliding_binder_must_still_happen() {
    must_verify(
        "substitution_under_binder_must_verify",
        "`n` is FREE inside `forall|k|` and must be replaced by the argument 7",
    );
    must_refute(
        "substitution_under_binder_must_refute",
        "if the free `n` were dropped instead of substituted, argument 0 would \
         no longer be refuted",
    );
}

/// THE OTHER UNSOUND DIRECTION, pinned explicitly: leaving a free parameter
/// occurrence alone lets it re-bind to a same-named local in the CALLER.
#[test]
fn free_occurrence_must_not_rebind_to_a_caller_local() {
    must_refute(
        "caller_local_shadow_must_refute",
        "the obligation is `200 <= 100`, not the caller's `m == 5`",
    );
    must_verify(
        "caller_local_shadow_must_verify",
        "a caller local sharing the parameter's name must not block a legal call",
    );
}

/// The argument expression naming the callee's binder — capture of the
/// REPLACEMENT rather than of the occurrence. This lane was already correct;
/// pinned in both directions so the scope stack cannot regress it.
#[test]
fn argument_named_like_the_binder_is_unchanged() {
    must_verify(
        "arg_named_like_binder_must_verify",
        "argument 7 satisfies `n >= 1` even though the local is named `k`",
    );
    must_refute(
        "arg_named_like_binder_must_refute",
        "argument 0 fails `n >= 1`",
    );
}

/// The overwhelmingly common shape: no quantifier anywhere. Both directions.
#[test]
fn plain_contracts_are_untouched() {
    must_verify("plain_requires_must_verify", "`9 >= 1`");
    must_refute("plain_requires_must_refute", "`0 >= 1` is false");
    must_verify("plain_ensures_must_verify", "`result == 4` is assumable");
    must_refute("plain_ensures_must_refute", "`r == 5` does not follow");
}

/// `let` in a contract clause is the other live binder form. A block local
/// scopes over the REST of the block while its INITIALIZER is evaluated in the
/// scope BEFORE the binding, so a scope pushed one statement too early or too
/// late shows up here and nowhere else.
#[test]
fn let_bindings_inside_a_clause_are_scoped_by_statement() {
    must_refute(
        "let_local_shadow_must_refute",
        "`{ let n = 0; n >= 1 }` is false for every argument",
    );
    must_verify(
        "let_initializer_must_verify",
        "the `n` in `let q = n` is FREE and must take the argument 9",
    );
    must_refute(
        "let_initializer_must_refute",
        "the same initializer with argument 0 fails `q >= 1`",
    );
}
