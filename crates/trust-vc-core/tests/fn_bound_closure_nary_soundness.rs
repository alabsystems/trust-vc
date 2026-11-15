// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for LANE 1a (Fn-bound n-ary application) —
//! the ARITY-N widening of the Fn-bound closure lane (Increments 1 / 2a / 2b,
//! previously UNARY). An `F: Fn(A, B, ..) -> R`-bounded value parameter `f: F` is
//! typed as a first-class `SpecFn(A, B, .., R)` value; an application
//! `f(a, b, ..)` lowers to the opaque, congruent `spec_fn_apply` UF over the
//! N-TUPLE, and the callee-side obligation / cross-boundary pass-site linkage
//! generalize verbatim.
//!
//! WHY THIS IS SOUND AND NON-TRIVIAL (per arity ≥ 2, plus 0 / 3 sanity):
//! * One congruent UF per signature: equal argument TUPLES are one term. An `Fn`
//!   closure can read shared state, so two applications may differ at run time,
//!   and the `Verified` answer of `f(3,4) == f(3,4)` is refused; distinct args
//!   (`f(3,4) == f(3,5)`) and a concrete pin (`f(3,4) == 7`) COUNTEREXAMPLE.
//!   `arg_type_key` makes the UF per-signature, so a 2-ary and a 1-ary `Fn`
//!   never collide.
//! * The callee-side obligation is the SOUND conditional assume over the opaque
//!   n-ary UFs: `call_requires%(f, (a,b)) ==> call_ensures%(f, (a,b), f(a,b))`.
//!   The prove-requires GATES the assume-ensures: a callee using `f.ensures`
//!   WITHOUT establishing `f.requires` fails closed. `call_ensures%` stays OPAQUE,
//!   so a concrete pin and an anti-vacuity wrong-return both counterexample.
//! * Pass-site linkage bridges a passed n-ary `closure!` literal's OWN concrete
//!   spec to those opaque UFs; a requires-violation, a false-ensures-use, and a
//!   lying closure (def-side sinks the caller) all counterexample, and a re-passed
//!   Fn-bound PARAM (never a registered literal) fails closed.
//! * `FnMut`/`FnOnce` are non-deterministic and stay fail-closed at EVERY arity.
//! * H6: the application PROVES `f.requires((args..))` (Verus/vstd
//!   semantics); the determinism fixtures declare it and have requires-free
//!   `*_no_requires_cx` twins refuted on `__call_requires_pp*_f_*`, and the traps
//!   declare every applied tuple's requires so they land on the ASSERTION.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify. Acceptance probes require exactly `Verified`, Counterexample
//! probes require exactly `Counterexample`, and `assert_not_verified` treats an
//! extraction `Err` and any solver non-`Verified` (incl. `Unknown`) as a sound
//! non-verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/fn_bound_closure_nary_soundness_repro.rs",
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
        "`{func}` should VERIFY (sound n-ary `Fn` obligation / linkage); got {v:?}"
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

/// Assert an exact `Counterexample` — stronger than "not verified": it witnesses
/// that the n-ary `spec_fn_apply` / obligation term is LOAD-BEARING (a live term
/// the solver can falsify), rather than the term being absent (an "Undefined
/// function" error).
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE (n-ary term modeled but not pinned); got {v:?}"
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
        panic!("FN-BOUND N-ARY FALSE-VERIFY: `{func}` must not verify")
    }
}

// --- TYPING / DETERMINISM (arity-2) ---------------------------------------

#[test]
fn t1_nary2_determinism_refused() {
    // The refusal comes only from a `Verified` answer, which needs `f: F` typed
    // `SpecFn(u64,u64,u64)` and `f(3,4)` lowered to the congruent `spec_fn_apply`
    // UF over the 2-tuple (without it, a fail-closed "Undefined function: f").
    assert_refused("nary2_determinism_refused");
}

#[test]
fn t1b_nary2_determinism_no_requires_cx() {
    assert_cx_on("nary2_determinism_no_requires_cx", "__call_requires_pp");
}

#[test]
fn t2_nary2_determinism_where_clause_refused() {
    assert_refused("nary2_determinism_where_clause_refused");
}

#[test]
fn t2b_nary2_determinism_where_clause_no_requires_cx() {
    assert_cx_on(
        "nary2_determinism_where_clause_no_requires_cx",
        "__call_requires_pp",
    );
}

#[test]
fn t3_nary2_distinct_args_counterexample() {
    // Distinct second arg: congruence gives nothing.
    assert_cx_on("nary2_distinct_args_cx", "assertion_");
}

#[test]
fn t4_nary2_concrete_trap_counterexample() {
    // Unconstrained result; a concrete pin is not provable.
    assert_cx_on("nary2_concrete_trap_cx", "assertion_");
}

// --- OBLIGATION (2a n-ary) -------------------------------------------------

#[test]
fn t5_nary2_obligation_positive_verified() {
    assert_verified("nary2_obligation_positive");
}

#[test]
fn t6_nary2_obligation_positive_let_verified() {
    assert_verified("nary2_obligation_positive_let");
}

#[test]
fn t7_nary2_obligation_pins_concrete_result_counterexample() {
    // TRAP #1: ensures derivable but opaque — no concrete value pinned.
    assert_counterexample("nary2_obligation_pins_concrete_result_cx");
}

#[test]
fn t8_nary2_obligation_missing_requires_counterexample() {
    // TRAP #2 (the crux): uses `f.ensures` without declaring `f.requires`.
    assert_counterexample("nary2_obligation_missing_requires_cx");
}

#[test]
fn t9_nary2_obligation_wrong_return_counterexample() {
    // ANTI-VACUITY: declares requires + ensures but returns a value other than
    // `f(a, b)`.
    assert_counterexample("nary2_obligation_wrong_return_cx");
}

// --- PASS-SITE (2b n-ary) --------------------------------------------------

#[test]
fn t10_nary2_pass_site_positive_verified() {
    assert_verified("nary2_pass_site_positive");
}

#[test]
fn t11_nary2_pass_site_requires_violation_counterexample() {
    assert_counterexample("nary2_pass_site_requires_violation_cx");
}

#[test]
fn t12_nary2_pass_site_false_ensures_use_counterexample() {
    assert_counterexample("nary2_pass_site_false_ensures_use_cx");
}

#[test]
fn t13_nary2_pass_site_lying_closure_counterexample() {
    // The closure's independent def-side counterexample must sink the caller and
    // must NOT be masked by the faithful 2b linkage.
    assert_counterexample("nary2_pass_site_lying_closure_cx");
}

#[test]
fn t14_nary2_pass_site_param_repass_fail_closed() {
    // A re-passed Fn-bound PARAM is not a registered literal ⇒ no ground fact ⇒
    // the opaque requires is undischargeable ⇒ fails closed.
    assert_not_verified("nary2_pass_site_param_repass_fail_closed");
}

// --- REGRESSION / FAIL-CLOSED / ARITY SANITY -------------------------------

#[test]
fn t15_fnmut2_fail_closed() {
    // `FnMut` at arity-2 stays fail-closed (not typed `SpecFn`; the application is
    // rejected at extraction). A `Verified` = congruence leaked to a
    // non-deterministic bound.
    assert_not_verified("fnmut2_fail_closed");
}

#[test]
fn t16_fnonce2_fail_closed() {
    assert_not_verified("fnonce2_fail_closed");
}

#[test]
fn t17_nary0_determinism_refused() {
    // Arity-0 sanity: `f() == f()` is one congruent term over the empty tuple,
    // and a nullary `Fn` closure can return a counter.
    assert_refused("nary0_determinism_refused");
}

#[test]
fn t17b_nary0_determinism_no_requires_cx() {
    assert_cx_on("nary0_determinism_no_requires_cx", "__call_requires_pp");
}

#[test]
fn t18_nary0_concrete_trap_counterexample() {
    assert_cx_on("nary0_concrete_trap_cx", "assertion_");
}

#[test]
fn t19_nary3_determinism_refused() {
    assert_refused("nary3_determinism_refused");
}

#[test]
fn t19b_nary3_determinism_no_requires_cx() {
    assert_cx_on("nary3_determinism_no_requires_cx", "__call_requires_pp");
}

#[test]
fn t20_nary3_distinct_args_counterexample() {
    assert_cx_on("nary3_distinct_args_cx", "assertion_");
}

#[test]
fn t21_nary3_obligation_positive_verified() {
    assert_verified("nary3_obligation_positive");
}
