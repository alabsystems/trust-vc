// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for INCREMENT 2a of Fn-bound closure
//! dispatch (the callee-side obligation model): at a Fn-bound call `let r = f(a)`
//! (where `f: F`, `F: Fn(A) -> B` is typed `SpecFn` by Increment 1) the callee
//! can now USE the closure's spec through the OPAQUE reflection UFs
//! `call_requires%` / `call_ensures%`.
//!
//! THE SOUND MODEL (a proven precondition plus a conditional assume over opaque
//! UFs, reusing the `add_helper_contract_obligations` drop discipline; the PROVE
//! is H6 — Verus/vstd call semantics):
//!
//!     PROVE   call_requires%(f, a)
//!     ASSUME  call_requires%(f, a)  ==>  call_ensures%(f, a, f(a))
//!
//! binding the REAL returned `spec_fn_apply(f, a)` term. This is the closure's
//! OWN contract and is unconditionally valid for ANY closure satisfying `F: Fn`.
//!
//! CRUX — prove-requires GATES assume-ensures:
//! * `call_ensures%` is NEVER usable unconditionally. It is derivable ONLY once
//!   `call_requires%(f, a)` is independently established — from the callee's own
//!   `requires f.requires((a,))` (an ASSUMED `call_requires%`) or an explicit
//!   `assume!`. A callee that uses `f.ensures` WITHOUT establishing the
//!   (non-trivial, opaque) `f.requires` cannot derive the postcondition and fails
//!   closed (TRAP #2). This is the load-bearing soundness gate.
//! * `call_ensures%` stays OPAQUE — it pins NO concrete value, so a concrete
//!   claim about the result (`assert!(f(a) == 5)`) is not provable (TRAP #1). The
//!   callee never invents a def-side for the def-side-less parameter, so the
//!   direct-application cardinal invariant is not weakened.
//! * The Increment-1 congruent term is untouched: `f(3) == f(3)` is still proved
//!   from congruence once `requires f.requires((3,))` is declared (its
//!   `Verified` answer is refused, since a stateful `Fn` closure returns two
//!   values; its requires-free twin is refuted on the call-site requires), and a
//!   concrete pin (`f(3) == 3`) still counterexamples. FnMut/FnOnce stay
//!   fail-closed.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/fn_bound_closure_obligation_soundness_repro.rs",
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

/// Assert the refusal of a `Verified` answer for a callable parameter evaluated
/// more than once. Only a `Verified` answer produces it, so a refutation here
/// still fails the assertion.
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

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY (conditional assume + established requires \
         discharges the opaque ensures); got {v:?}"
    );
}

/// Assert an exact `Counterexample` — stronger than "not verified": it witnesses
/// that the seam is LOAD-BEARING (a live obligation the solver can falsify),
/// rather than the term being absent (an "Undefined function" error).
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE; got {v:?}"
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

fn assert_not_verified(func: &str) {
    // An extraction Err (deferred / fail-closed lowering) or any solver
    // non-Verified verdict (incl. Unknown) is a sound non-verify.
    if let Ok(VerifyResult::Verified) = verify(func) {
        panic!("FN-BOUND OBLIGATION FALSE-VERIFY: `{func}` must not verify")
    }
}

#[test]
fn t1_positive_tail_verified() {
    // POSITIVE: declares `requires f.requires((a,))` + `ensures f.ensures((a,),
    // result)`, body `f(a)`. The call-site conditional assume + the assumed
    // precondition derive the opaque ensures. The load-bearing success signal.
    assert_verified("fnbound_obligation_positive_tail");
}

#[test]
fn t2_positive_let_verified() {
    // POSITIVE (let form): the application on a `let`-RHS (straight-line seam).
    assert_verified("fnbound_obligation_positive_let");
}

#[test]
fn t3_pins_concrete_result_counterexample() {
    // FALSE-VERIFY TRAP #1: the ensures IS derivable (requires declared), but
    // `call_ensures%` is OPAQUE — it pins no concrete value, so `r == 5` is not
    // provable. A `Verified` = inventing a concrete result = UNSOUND.
    assert_counterexample("fnbound_obligation_pins_concrete_result_cx");
}

#[test]
fn t3b_wrong_return_counterexample() {
    // ANTI-VACUITY: declares requires + ensures but returns a value OTHER than
    // `f(a)`. The assume binds `call_ensures%(f, a, f(a))`, not the returned `5`,
    // so the postcondition is not derivable. A `Verified` = the ensures is
    // trivially true / the assume bound an arbitrary value = UNSOUND.
    assert_counterexample("fnbound_obligation_wrong_return_cx");
}

#[test]
fn t4_missing_requires_counterexample() {
    // FALSE-VERIFY TRAP #2 (the crux): USES `f.ensures` as the postcondition but
    // declares NO `requires f.requires`. `call_requires%` is unconstrained, so the
    // conditional assume cannot fire and the ensures is underivable. A `Verified`
    // = using the ensures without discharging the requires = UNSOUND. Since H6 the
    // tail application also emits its own unprovable call-site prove-requires;
    // the measured first refuted obligation is the `postcondition`.
    assert_counterexample("fnbound_obligation_missing_requires_cx");
}

#[test]
fn t5_missing_requires_assert_counterexample() {
    // TRAP #2 companion (assert form): `assert!(f.ensures((a,), r))` without a
    // declared requires. Same gate — the ensures is underivable, and (H6) the
    // application's call-site requires is refuted first.
    assert_cx_on(
        "fnbound_obligation_missing_requires_assert_cx",
        "__call_requires_pp",
    );
}

#[test]
fn t6_determinism_refused_not_refuted() {
    // REGRESSION (Increment 1 intact): two calls WITHOUT a requires clause are
    // still proved equal from the congruent term alone, and that `Verified`
    // answer is refused. The seam adds ONLY a conditional assume (inert, result
    // unused), NO standalone obligation a requires-free call could fail. A
    // Counterexample here = the seam over-constrained the term.
    assert_refused("fnbound_obligation_determinism_refused");
}

#[test]
fn t6b_determinism_no_requires_counterexample() {
    // H6: requires-free determinism was a whole-program false verify (the
    // requires was only an assumed antecedent). The call-site prove-requires is
    // now emitted and refuted.
    assert_cx_on(
        "fnbound_obligation_determinism_no_requires_cx",
        "__call_requires_pp",
    );
}

#[test]
fn t7_pins_concrete_no_requires_counterexample() {
    // REGRESSION: a concrete pin `f(3) == 3` still counterexamples (unconstrained
    // result, no matching ensures to derive a value). With no requires declared,
    // H6's call-site prove-requires is the refuted obligation.
    assert_cx_on(
        "fnbound_obligation_pins_concrete_no_requires_cx",
        "__call_requires_pp",
    );
}

#[test]
fn t8_fnmut_fail_closed() {
    // REGRESSION: `FnMut` stays fail-closed (not typed `SpecFn`; H6 rejects the
    // application at extraction with a "function value" diagnostic).
    assert_not_verified("fnbound_obligation_fnmut_fail_closed");
}

#[test]
fn t9_fnonce_fail_closed() {
    // REGRESSION: `FnOnce` stays fail-closed.
    assert_not_verified("fnbound_obligation_fnonce_fail_closed");
}
