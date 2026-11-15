// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for INCREMENT 1 of Fn-bound closure dispatch
//! (the typing foundation): an `F: Fn(A..) -> B`-bounded value parameter `f: F`
//! is typed as a first-class `SpecFn(A.., B)` value, so a call `f(x)` reaches the
//! existing opaque, congruent `spec_fn_apply` UF
//! (`ir_lowering/dispatch/calls.rs`).
//!
//! WHAT THE TYPING GIVES:
//! * Reflexivity of one call (`let o = f(3); o == o`) VERIFIES.
//! * Two calls with the same arguments are one term of the congruent UF, but an
//!   `Fn` closure can read shared state (an atomic, a borrowed `Cell`), so
//!   `f(3) == f(3)` is false at run time. `bodiless_call_repeat` refuses the
//!   `Verified` answer of a function that evaluates a callable parameter twice.
//! * The result is otherwise UNCONSTRAINED: `f(3) == 3` (pinning a concrete
//!   value) and `f(3) == f(4)` (different args) COUNTEREXAMPLE. A `Verified` on
//!   either would be inventing behaviour = UNSOUND.
//! * `FnMut`/`FnOnce` are non-deterministic across calls; typing them as a
//!   congruent `SpecFn` would unsoundly prove `f(3) == f(3)`. They are left
//!   UNMODELED and stay fail-closed (the call fails to lower).
//!
//! CRUX (def-side-less parameter vs the direct-application cardinal invariant):
//! a `Fn` parameter has NO def-side body. Typing it as `SpecFn` registers NO
//! reflection contract and runs NO def-side obligation, so nothing is ASSUMED
//! about the result (no `call_ensures%` axiom, no `record_closure_def_side_failure`
//! trip). The invariant "SpecFn-typed ⟺ registered-with-checked-def-side" is not
//! weakened — a def-side-less parameter never enters the registered/assumed lane.
//! The traps below (Counterexample, NOT "Undefined function" error) are the
//! load-bearing witness that the term is modeled yet unconstrained.
//!
//! H6: every application PROVES `f.requires((args,))` (Verus/vstd
//! semantics), so the positive fixtures declare the requires they apply under
//! and each has a requires-free `*_no_requires_cx` twin that counterexamples on
//! the call-site `__call_requires_pp*_f_*` obligation; the traps are pinned to
//! the ASSERTION (the requires is discharged), and FnMut / FnOnce applications
//! fail closed at extraction with a "function value" diagnostic.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify. `assert_not_verified` treats an extraction `Err` and any solver
//! non-`Verified` (incl. `Unknown`) as a sound non-verify; acceptance probes
//! require exactly `Verified` and Counterexample probes require exactly
//! `Counterexample`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/fn_bound_closure_typing_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    // SOUNDNESS-CRITICAL: recompute every verdict cache-off. A single stale
    // `Verified` would otherwise be served forever and mask a real false-verify.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY (reflexivity of one call); got {v:?}"
    );
}

/// Assert an exact `Counterexample`. This is stronger than "not verified": it
/// witnesses that the `SpecFn` typing is LOAD-BEARING — the call lowered to a
/// live `spec_fn_apply` term that the solver can falsify — rather than the term
/// being absent (an "Undefined function" error).
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE (unconstrained result, term is modeled but \
         not pinned); got {v:?}"
    );
}

/// Assert the refusal of a `Verified` answer for a callable parameter evaluated
/// more than once. Only a `Verified` answer produces it.
fn assert_refused(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(
            &v,
            VerifyResult::Error { message } if message.starts_with("bodiless call repeated")
        ),
        "`{func}` should be REFUSED (a callable parameter evaluated twice); got {v:?}"
    );
}

/// A Counterexample on an obligation whose name starts with `prefix`.
fn assert_cx_on(func: &str, prefix: &str) {
    let v = verdict(func);
    match &v {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with(prefix) => {}
        _ => panic!("`{func}` should COUNTEREXAMPLE on a `{prefix}*` obligation; got {v:?}"),
    }
}

/// H6: an application of an unmodelled function value fails closed at
/// extraction with the "function value" diagnostic (never a lowering error that
/// an unused result would skip).
fn assert_function_value_fail_closed(func: &str) {
    let message = match verify(func) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => panic!("FN-BOUND: `{func}` should fail closed at extraction; got {other:?}"),
    };
    assert!(
        message.contains("function value"),
        "`{func}` failed closed without the \"function value\" diagnostic: {message}"
    );
}

#[test]
fn t1_reflexive_verified() {
    // TARGET: reflexivity of a call through the bound. The load-bearing success
    // signal — verifies ONLY if `f: F` is typed `SpecFn` and `f(3)` lowers to the
    // congruent `spec_fn_apply` UF (without the typing this is a fail-closed
    // "Undefined function: f").
    assert_verified("fnbound_reflexive_verified");
}

#[test]
fn t1b_reflexive_no_requires_cx() {
    // H6: the same read without `requires f.requires((3,))` is refuted on the
    // call-site requires.
    assert_cx_on("fnbound_reflexive_no_requires_cx", "__call_requires_pp");
}

#[test]
fn t2_determinism_refused() {
    // Two calls with EQUAL arguments are one congruent term, but a stateful `Fn`
    // closure returns two values, so the `Verified` answer is refused.
    assert_refused("fnbound_determinism_refused");
}

#[test]
fn t2b_determinism_no_requires_cx() {
    assert_cx_on("fnbound_determinism_no_requires_cx", "__call_requires_pp");
}

#[test]
fn t3_determinism_where_clause_refused() {
    // Same, via the `where F: Fn(..)` spelling (where-predicate recognition path).
    assert_refused("fnbound_determinism_where_clause_refused");
}

#[test]
fn t3b_determinism_where_clause_no_requires_cx() {
    assert_cx_on(
        "fnbound_determinism_where_clause_no_requires_cx",
        "__call_requires_pp",
    );
}

#[test]
fn t4_pins_concrete_result_counterexample() {
    // FALSE-VERIFY TRAP #1: the result is UNCONSTRAINED; `f(3) == 3` is not
    // provable. A `Verified` here = inventing behaviour = UNSOUND. Must be a
    // Counterexample (NOT an "Undefined function" error), proving the typing is
    // load-bearing. The requires is discharged, so it lands on the ASSERTION.
    assert_counterexample("fnbound_pins_concrete_result_cx");
    assert_cx_on("fnbound_pins_concrete_result_cx", "assertion_");
}

#[test]
fn t5_distinct_args_counterexample() {
    // FALSE-VERIFY TRAP #2: DIFFERENT arguments — congruence gives nothing, so
    // `f(3) == f(4)` counterexamples — on the ASSERTION.
    assert_counterexample("fnbound_distinct_args_cx");
    assert_cx_on("fnbound_distinct_args_cx", "assertion_");
}

#[test]
fn t6_fnmut_determinism_must_not_verify() {
    // FnMut UNSOUNDNESS TRAP: `FnMut` is non-deterministic across calls, so
    // `f(3) == f(3)` must NOT be provable. `FnMut` is not typed as a congruent
    // `SpecFn`; the call stays fail-closed. A `Verified` = congruence leaked to
    // `FnMut` = UNSOUND.
    assert_function_value_fail_closed("fnmut_determinism_must_not_verify");
}

#[test]
fn t7_fnonce_reflexive_must_not_verify() {
    // FnOnce companion: also excluded from the congruent `SpecFn` typing, so even
    // the reflexive shape stays fail-closed (the call does not lower).
    assert_function_value_fail_closed("fnonce_reflexive_must_not_verify");
}
