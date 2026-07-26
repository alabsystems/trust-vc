// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for INCREMENT 1 of Fn-bound closure dispatch
//! (the typing foundation): an `F: Fn(A..) -> B`-bounded value parameter `f: F`
//! is typed as a first-class `SpecFn(A.., B)` value, so a call `f(x)` reaches the
//! existing opaque, congruent `spec_fn_apply` UF
//! (`ir_lowering/dispatch/calls.rs`).
//!
//! WHY THIS IS SOUND AND NON-TRIVIAL:
//! * `Fn` captures immutably ⇒ DETERMINISTIC across calls, so one congruent UF is
//!   sound: equal arguments give the equal result. Reflexivity (`f(3) == f(3)`)
//!   AND determinism (two calls, same args) VERIFY — the latter is the real,
//!   non-tautological capability the typing delivers.
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
        "`{func}` should VERIFY (sound `Fn` determinism / reflexivity); got {v:?}"
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

fn assert_not_verified(func: &str) {
    match verify(func) {
        Ok(VerifyResult::Verified) => {
            panic!("FN-BOUND FALSE-VERIFY: `{func}` must not verify")
        }
        // An extraction Err (deferred / fail-closed lowering) or any solver
        // non-Verified verdict (incl. Unknown) is a sound non-verify.
        _ => {}
    }
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
fn t2_determinism_verified() {
    // DETERMINISM (non-tautological, SOUND): two calls with EQUAL arguments give
    // the EQUAL result via congruence. The genuine capability of Increment 1.
    assert_verified("fnbound_determinism_verified");
}

#[test]
fn t3_determinism_where_clause_verified() {
    // Same, via the `where F: Fn(..)` spelling (where-predicate recognition path).
    assert_verified("fnbound_determinism_where_clause_verified");
}

#[test]
fn t4_pins_concrete_result_counterexample() {
    // FALSE-VERIFY TRAP #1: the result is UNCONSTRAINED; `f(3) == 3` is not
    // provable. A `Verified` here = inventing behaviour = UNSOUND. Must be a
    // Counterexample (NOT an "Undefined function" error), proving the typing is
    // load-bearing.
    assert_counterexample("fnbound_pins_concrete_result_cx");
}

#[test]
fn t5_distinct_args_counterexample() {
    // FALSE-VERIFY TRAP #2: DIFFERENT arguments — congruence gives nothing, so
    // `f(3) == f(4)` counterexamples.
    assert_counterexample("fnbound_distinct_args_cx");
}

#[test]
fn t6_fnmut_determinism_must_not_verify() {
    // FnMut UNSOUNDNESS TRAP: `FnMut` is non-deterministic across calls, so
    // `f(3) == f(3)` must NOT be provable. `FnMut` is not typed as a congruent
    // `SpecFn`; the call stays fail-closed. A `Verified` = congruence leaked to
    // `FnMut` = UNSOUND.
    assert_not_verified("fnmut_determinism_must_not_verify");
}

#[test]
fn t7_fnonce_reflexive_must_not_verify() {
    // FnOnce companion: also excluded from the congruent `SpecFn` typing, so even
    // the reflexive shape stays fail-closed (the call does not lower).
    assert_not_verified("fnonce_reflexive_must_not_verify");
}
